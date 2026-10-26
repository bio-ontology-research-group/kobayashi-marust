---
name: km-bridge-disjunction-probe
description: "konclude_ht bridge on the disjunction-family timeouts — 12653 SOLVED (d64e78b, DDB-green 93e62e4); 541 DDB analysis now WORKS but needs per-branch databox COW (the convergent next piece, also = 3215 databox reuse)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

# konclude_ht bridge vs the disjunction-family timeouts (2026-07-06)

Question: does Konclude's algorithm (via the deterministic bridge, post-5099d52)
terminate on the disjunction-family onts that production km times out on?

## ore_ont_12653: SOLVED — sound+complete in 1.0 s (commit d64e78b)
Production km times out (240 s); the bridge classifies it **missing=0
spurious=0 elapsed=1.0s** (subjects=14, all nondet → pairwise fallback).
What it took (all faithful Konclude ports, in d64e78b):
1. **domain/range**: bridge fills `Role::{domain,range}_linker` from
   `R(x,y)→C(x)/C(y)` clauses; u08 `ht_apply_role_domain_range` applies them
   at EVERY link install (base + per-super-role + mirror-inverse), the exact
   createNewIndividualsLink* placement (cpp 22303–22334 / 22382–22395).
2. **inverse-role hierarchy**: `R(x,y)→S(y,x)` = `R ⊑ S⁻` as a PLAIN super
   entry against the concrete inverse-role object; closure over both
   polarities (also fixes latent `R⊑S ⇒ R⁻⊑S⁻` for mirror edges). NB
   `has_indirect_super_role` ignores the negated flag — polarity must resolve
   to distinct role objects, never the flag.
3. **card_defs**: first-class qualified CCATLEAST/CCATMOST from
   `cb_to_ht::convert(card_enabled=true)`, absorbed onto the marker concept.
4. **pairwise fallback**: nondet subject read-off not authoritative →
   pairwise `bridged_unsat(s ⊓ ¬sup)` probes (sound on any branch discipline).

Regression: 1016 read-off IDENTICAL (32712/32739, spurious=0, nondet=0, 54 s);
konclude_ht suite 1208/1208.

## ore_ont_541: NO — pure backtrack thrashing, NOT model explosion
Instrumented with `KM_BRIDGE_PROGRESS=1` (u02 per-drive counters, committed):
- nodes = **4, flat** for the entire run; 2.6M chronological backtracks/120 s;
  or_branch_stack depth pinned at **55–56** → enumerating ~2^56 branch space.
- UNCHANGED by the d64e78b coverage wave (search discipline, not coverage).

**Why:** 541-style onts stack deep independent disjunctions; a clash near the
bottom does not depend on most branch points above it. DDB backjumps over
them; chronological search re-enumerates the full product space — no constant
factor saves it.

**How to apply:** next konclude_ht port wave = u29 `clashedBacktracking` +
Unit 28/30 tracking-line records + arena/databox watermark restore, from
Konclude source (~/Public/software/Konclude), per [[feedback-port-from-konclude]].
Diagnostics: `KM_BRIDGE_PROGRESS=1` prints `PROGRESS drives= backtracks=
nodes= inserts= bp_depth=` every 4096 drives and `PROGRESS-SAT iters=` every
1M in-drive iterations. See also [[project_km_bridge_nondeterminism]].

## 2026-07-07 update: the DDB wave landed (ca772f1 + 93e62e4)

u29 wiring is LIVE behind `KM_HT_DDB`: per-alternative nondet track points
minted upfront (u03), clashes routed through `clashed_backtracking`,
scan-then-mutate backjump walk with chronological fallback, root-cancel flag.
The dependency-spine gaps that had to be closed before the analysis could
run at all (each measured, all in 93e62e4):
1. ls1 `con_des_dep_track_point` is a ctx-less STUB returning NONE → every
   insert-clash partner read "untracked" → tracking ERROR → analysis aborted
   (ddb_marks=0, fallbacks=100%). Fixed caller-side (u36 insert, u09 trigger
   scan): resolve `conDes.get_dependency_track_point()` after the lookup.
   OTHER ls1 lookup out-tp consumers still stubbed — same fix applies.
2. Seeds must carry the INDEPENDENT base dependency track point
   (`get_or_create_base_dependency_track_point`), never NONE.
3. u09 implication rule passed trigger_deps=NONE → heads fired by
   branch-added triggers inherited base tag 0 → clashes traced to level 0 →
   WRONG ROOT-CANCEL (12653 spurious=4). Fix = per-satisfied-trigger
   CONNECTION dependency nodes chained as additional-dependency links
   (depended_branching_tag walks additional_after).
4. Semantic branching (atomic, Konclude default) is sound ONLY on a restored
   snapshot — on an unrestored label it manufactures false clashes (12653
   spurious=120). Gated on `restored`.
5. Leftover guard: any advance-without-restore disables the pop-unmarked
   backjump (stale tps break the level-ordering argument; 12653 spurious=4
   via that path too). Root-cancel stays valid (leftovers have tags>0).

Result: 12653 missing=0 spurious=0 with DDB on AND off; suite 1208/1208.

**541 after the wave**: the analysis WORKS (probes root-cancel in ms;
readoffs complete: `SUBJ 3 Cell: readoff 305 supers 0.0s`), BUT with the
dependency spine on, blocking becomes dependency-aware → nodes grow 4→8591
→ restore guard trips → leftover guard forces chronological on the deep
subjects (SUBJ 6 Process: 27.9s, 1M backtracks). The convergent next piece:
**per-branch databox COW/localization** (db1–db6 + db2 localizing getters +
individual_process_node_vector local/parent split are ALL ported substrate).
It makes restores always possible (guard removable, semb sound everywhere)
AND gives 3215 its per-subject databox reuse — one implementation, both
blockers. `KM_HT_BRIDGE_RECOG` (≥k-recognition eq-head encoder) exists but
is OFF: it caused 3 spurious pairs on 12653 (qualified-atmost merge
suspected); root-cause before enabling.

Production wiring (also in ca772f1): `bridged_classify` +
`KM_HT_BRIDGE` arm in tableau::run_json + `bridge_candidate` route in
spawn_ht with `KM_HT_BRIDGE_ONLY` defer. Blocker for 12653 in production:
unsupported=37 (the eq-head recognition clauses) → driver declines.

## 2026-07-07 COW landed (d5603a0) + 541 residual bug PINPOINTED (7549697)

COW works: with `KM_HT_DDB=1 KM_HT_COW=1` the 541 subject that thrashed
1M+ backtracks decides in 16 ms / 435 backtracks (arena epoch journals +
databox snapshots; the dependency SPINE + clash_descs + con_descs are
epoch-EXEMPT — branch-shared memory, truncating them dangled ids in
persisted DDB clash sets → panic in u30
get_collected_filtered_clashed_descriptors_from_branch). COW cost is
high (uniform first-touch journal: 12653 DDB 0.9s→260s), so it stays
opt-in; next perf step = per-node localization + pruned snapshot, or an
adaptive no-COW-then-COW-on-budget-trip retry.

**But 541 is NOT solved** — DDB+COW exposed a SEPARATE bridge
soundness/coverage bug (not the search machinery; reproduces at
baseline completion): the bridge spuriously makes **Cell
UNSATISFIABLE** (gold: Cell ⊑ {Compound, Condition, MaterialObject,
Particular, PolyMolecularCompositeEntity, StructuredBiologicalEntity},
Wave NOT among them; every pairwise Cell⊑X then comes back true = 50
spurious). Provenance (KM_BRIDGE_WATCH_NODE/WATCH_ALL/WATCH_IMPL, all
committed): the `projectsOnto`-successor node gets
`ImmaterialThreeDimensionalPhysicalEntity` (the ∃ filler of
`MaterialObject ⊑ ∃projectsOnto.Immaterial3D`) AND, via a
∀projectsOnto reapply (edge role == forall role == projectsOnto tag
107), `PointInTime`; `PointInTime ⊑ TemporalRegion` then clashes with
the disjoint-derived `¬TemporalRegion`. Real 541 axioms include BOTH
`MaterialObject ⊑ ∀projectsOnto.(Immaterial3D ⊓ EntityAtSomeTime)` and
some `X ⊑ ∀projectsOnto.PointInTime`. So the question to answer next
session: does Cell DETERMINISTICALLY entail `∀projectsOnto.PointInTime`
(baseline trace showed `consistent=false backtracks=0` = clash with no
open branch to try)? If yes, the bridge is wrongly deriving that ∀ on
the root (encoding bug in the guarded-clause ∀-residue or the
both-polarity role closure putting extra supers on projectsOnto — dump
showed projectsOnto supers = [topObjectProperty, INV(isProjectionOf),
INV(topObjectProperty)]). **RULED OUT via WATCH-ALL**: the offending ∀'s
own role tag is 107 = projectsOnto ITSELF, not top — so it is NOT a
top-role closure leak. The ∀projectsOnto.PointInTime is a genuine ∀
concept installed on the root. So the remaining question is purely:
why does Cell get `∀projectsOnto.PointInTime` DETERMINISTICALLY
(baseline: consistent=false, backtracks=0)? NEXT STEP: find the source
clause whose ∀-residue is role=projectsOnto filler=PointInTime (grep
the frontend/TInput clause set) and trace why Cell entails its
antecedent — likely a guarded-clause ∀-residue built with the wrong
antecedent, or an absorption/semantic-branching promoting a disjunctive
∀ deterministically. If Cell genuinely entails it, gold/HermiT are
contested; otherwise it is the bridge encoding bug to fix.

Diagnostic envs (all committed, inert unless set): KM_BRIDGE_TAG_NAMES,
KM_BRIDGE_DUMP_ROLE_SUPERS, KM_BRIDGE_WATCH_TAG, KM_BRIDGE_WATCH_NODE,
KM_BRIDGE_DUMP_FORALL, KM_BRIDGE_MAX_DRIVES, KM_BRIDGE_PROBE_BUDGET_S.
gold_541.json (166 pairs) on ws /tmp.

## 2026-07-07 — 541 SOUNDNESS BUG FOUND + FIXED (a4a3ae6)

Root cause (via KM_BRIDGE_WATCH_* provenance): the u08 ∀-reapply
`ht_reapply_universal_restrictions` added each propagated operand to the
successor under only the EDGE's dependency track point, DROPPING the ∀
concept descriptor's own track point. Konclude's applyALLRule (cpp
16321-16340) builds one `createALLDependency` per ∀ whose continue point
depends on BOTH the ∀ descriptor's track point AND the edge's. When a ∀
is BRANCH-DEPENDENT — here `Q_70 ≡ ∀projectsOnto.PointInTime`, the frontend
DEFINER for the ∀-in-body of `InstantaneousProcess ≡ ∀projectsOnto.
PointInTime ⊓ Process` — a clash on the successor traced to the
deterministic edge instead of the disjunction that introduced the ∀, so
u29 root-cancelled at branching level 0 → bridge spuriously made **Cell
UNSATISFIABLE** (~50 spurious; gold: Cell has 6 real supers, Wave not
among them). Q_70 reaches the root via `apply_or_rule` (the global
definer-introduction disjunction `⊤ → Q_70 ∨ ∃projectsOnto.¬PointInTime`).

Fix (u08, a4a3ae6): thread the source ∀ descriptor `cd` with each
operand; per-∀ `create_all_dependency(cd-track-point, edge-track-point)`
(memoized by cd = the C++ allDepNodeCreated flag); add operands under the
ALL dependency continue point. Domain/range stays on the edge track point
(deterministic terminology, never branch-dependent — correct as-is).

Effect: `ddb_jumps` now track drives, `ddb_fallbacks=0`, nodes bounded
26-35 — DDB backjumps CORRECTLY instead of wrong-root-cancelling. suite
1208/1208, 12653 DDB spurious=0. **541 is now SOUND but THROUGHPUT-bound**:
the Cell probe thrashes (1.3M backtracks, bp_depth ~250-390) because the
definer-introduction disjunction fires on EVERY node and the ∃projectsOnto
chain deepens the search — the live-disjunction family wall
([[project_km_disjunction_blowup]]). Next lever for 541 SPEED (not
soundness): GUARD the definer-introduction — `∀R.C ⊓ B ⊑ X` only needs the
definer recognized on B-nodes, so emit `B → Def ∨ ∃R.¬C` not `⊤ → …` (a
frontend/cb_to_ht normalization change, analogous to KM_HT_CARD_GUARD_EM);
Cell is not a Process so the disjunction would then not fire on it at all.
The bridge sees the flat trigger-less clause and cannot guard it — the
guard must come from the normalizer that knows the equivalence structure.

LESSON (reusable): every rule that propagates a concept whose source can
be branch-dependent MUST thread that source's dependency track point, or
DDB loses provenance and root-cancels. Same class as the u09 trigger-
CONNECTION fix (93e62e4). Audit remaining propagation sites (some-rule
filler, automaton transitions) for the same pattern before trusting DDB
broadly.

## 2026-07-07 — production probe 0/8 + 12653 real blocker = VALUE IDENTITY

IBEX probe 48193934 (KM_HT_BRIDGE+DDB+COW, 600s/56GB, all 8 timeouts):
**0/8 solved in production**; 541 became MEMOUT (56GB in 51s) because
`race_cb_vs_ht` had NO RSS watchdog on the HT child (elc racer has one)
— fixed in race.rs: `KM_HT_MEM_GB` (default 12GB) kill-the-arm watchdog,
monotone-safe. 12653 in production declined then the LEGACY Ht panicked
("Eq s bound", hypertableau.rs:6807) — harmless (worker error), but shows
the decline path falls into an unvalidated arm.

**12653's remaining 3 unsupported (with RECOG on) = datatype value
identity**: `__dt__val__"2"^^xsd:integer(x) ∧ same(y) → x=y` (path-length
values 2/3/4 in the LOD-paths ont). A literal is ONE semantic object;
Konclude gets this natively from its databox literal handling — the
clausal frontend surfaces it as a role-free eq-head clause. Under-merged
value nodes plausibly ALSO caused the historical "3 spurious onto Path"
(mis-decided counting), so recognition may be innocent.

**Implemented (pending 12653-vs-gold validation): singleton-concept
merge** — bridge recognizes `C(v1)∧C(v2)→eq(v1,v2)` (general structural
rule) → `Bridged.singleton_concepts` → `algo.singleton_concepts`; kernel
u02 `ht_apply_singleton_merges` = deterministic SCAN-AT-FIXPOINT merge
(branch-safe by construction, pure function of current branch state; no
queue rollback needed), merges later-into-earlier via
`merge_individual_node_into` under `create_same_individual_merge_dependency`
joining BOTH carriers' track points (faithful DDB provenance). Fixpoint
only when a scan is dry (hooked at take_next=none in run_saturation_loop).
Unit test `singleton_concept_merge_value_identity_unsat` (verdict REQUIRES
the merge) green; konclude_ht suite 1209/1209. Committed d58c2b2 (with the
race.rs KM_HT_MEM_GB watchdog).

**12653 END-TO-END through the production arm for the FIRST time**
(no defer, RECOG+singleton = full coverage; 133 s no-DDB / 181 s DDB —
throughput is per-subject env rebuild, task #13). NOT yet gold-clean:
- no-DDB: **11 spurious, all `X ⊑ Path`** (¬Path effectively unsat at
  probe time; superset of the historical 3-spurious) → suspect = the
  RECOG arm's ≤(k−1) encoding hitting u08's DETERMINISTIC GREEDY atmost
  merge (the nondet merge branch is W3-DEFER; greedy wrong-pair ⇒
  spurious clash ⇒ the D disjunct forced ⇒ Path). 1 missing:
  PathOfLength4 ⊑ Path.
- DDB: **39 spurious** (adds MainPath ⊑ everything) → prime suspect =
  PHANTOM-NODE MERGES: without COW, chronologically-abandoned
  alternatives leave nodes in the arena; the global singleton scan sees
  an abandoned-branch val-carrier and merges the live one into it
  (u08's atmost merge never hits this — it scans only a node's current
  successors). DDB changes backtrack coverage → different phantom
  populations (39 vs 11 consistent with this).

NEXT (in order): (1) add KM_HT_NO_SINGLETON diagnostic gate for A/B;
(2) reproduce ONE probe (`Property ⊓ ¬Path`) in the harness with clash
provenance (KM_BRIDGE_WATCH_*) — decide phantom vs greedy; (3) fixes:
phantom → restrict the singleton scan to nodes REACHABLE from the
current probe root via live edges; greedy → port the nondeterministic
merge branch (or distinctness-aware pair selection) from Konclude
applyATMOSTRule cpp 14861+/15832 (choose-trigger machinery).

## 2026-07-07 (cont) — 12653 spurious root-cause chase: THREE fixes in, leak is CHRONOLOGICAL LEFTOVERS

Probe isolation (`bridge_probe_pair`, KM_BRIDGE_ONT + KM_BRIDGE_PAIR=
Property,Path + KM_HT_BRIDGE_RECOG=1): spurious pair reproduces —
`pairwise=true`, ZERO singleton merges (singleton/phantom EXONERATED for
this pair). New diagnostics (uncommitted): KM_BRIDGE_DUMP_CLASH (final
clash chain at the 3 return-false sites in run_completion_on),
KM_BRIDGE_DUMP_RECOG, KM_BRIDGE_WATCH_MERGE. Final clash decoded via
KM_BRIDGE_TAG_NAMES: `def_exfil_f_Q_44_2 @ n0` vs seeded `¬Path @ n0`
(chrono-exhausted, backtracks=18, bp_depth=0) — a frontend DEFINER
implying Path sits on the ROOT at exhaustion.

Fixes implemented this session (all uncommitted, suite 1209/1209 green
after each):
1. **u08 qualifier polarity** (`ht_role_successors_with_concepts`):
   count a successor toward ≤n R.C ONLY on positive-polarity containment
   (cpp 15879 `if (!containsNegation)`); rule-level negate does NOT flip
   filler polarity. Probe UNCHANGED (still pairwise=true).
2. **Nondet at-most merge branching** (port of
   `mergeMergingIndividualNodesPairwise` cpp 15044–15093):
   `BranchKind::AtMostMerge` OrBranchPoints whose alternatives = ALL
   mergeable pairs; pair 0 = old greedy pair (deterministic parity);
   u02 `advance_atmost_merge_alternative` performs sibling merges +
   bound re-check; `ht_mint_alternative_track_points` extracted from u03
   (shared DDB minting); MERGE dependency node per decision. KEY DESIGN:
   merge BPs ALWAYS own a branch epoch (`OrBranchPoint::own_epoch`),
   even no-COW — merges are not undoable by the single-node label
   snapshot; epoch push/pop/advance now keyed per-BP, not on the global
   conf_inprocess_cow. Probe UNCHANGED (identical clash + backtracks=18
   → merge alternatives never explored on this pair).
3. **Choose rule** (port of `qualifyMergingIndividualNodes` cpp
   15677–15816): `BranchKind::AtMostQualify` — a role successor deciding
   NEITHER qualifier polarity branches ¬C-first/C-second (C-alt becomes a
   merge candidate), both re-fire the at-most; ≤0 case qualifies ¬C
   deterministically; fires unconditionally (standard SHIQ choose), one
   candidate per rule fire. QUALIFY dependency as decision node.
   Not yet validated (build pending).

**Current hypothesis for the remaining pairwise=true**: NOT the at-most
machinery — the identical-clash evidence points at the KNOWN no-COW
chronological gap: a refuted successor-CREATING disjunct alternative
skips the label-snapshot restore (node_count guard), its derivations
(the definer) stay on n0 forever, later alternatives inherit them →
false clash cascade → spurious unsat. COW is the existing complete
restore; probe with KM_HT_COW=1 running. If COW is the fix, bridge
pairwise probes need COW-by-default (or adaptive no-COW→COW retry) +
the perf work (COW cost: 12653 DDB 0.9→260s uniform-journal).

## 2026-07-07 (cont-2) — LAZY TRIGGERED-OR: the 12653 probe fix (committed wave 1497954 + lazy-OR)

COW probes were a dead end operationally: COW-only >300s one pair, no
verdict; COW+DDB hit **117 GB RSS on ws** (killed by PID) — sound
restore exposes the true search space and the every-node disjunctions
explode it. KM_BRIDGE_DUMP_TOPGCI census (new env) on 12653: only **8
top-attached GCIs** out of 486 impls cause everything — 3 trigger-less
≥k-recognitions `⊤ ⊑ Q_k ∨ ≤(k−1)R0.PathElement` (PathOfLength2/3/4)
and 4 definer excluded-middle pairs `⊤ ⊑ Q_a ∨ Q_b`, +1 harmless.

**THE FIX (u03 initialize_or_processing, KM_HT_NO_LAZY_OR opt-out,
default ON)**: lazy triggered-OR — before branching a disjunction, if
some effectively-POSITIVE ATMOST operand's bound currently HOLDS under
the PESSIMISTIC successor count (u08
ht_role_successor_count_possibly_qualified: successors not decided
AGAINST the qualifier; undecided count), DEFER: register the OR's
descriptor on the at-most's role reapply queue and return without
branching. Sound (asserts nothing). COMPLETE: the pessimistic count
only grows via NEW role-links (undecided→C already counted;
undecided→¬C shrinks), and each new link re-fires the OR via the
role-keyed reapply — no successor-side ATMOSTReactivation needed. This
is the absorption/branching-trigger stand-in (Konclude
CConceptRoleBranchingTrigger).

Result: `Property ⊑ Path` probe **pairwise=false** (spurious GONE),
no-COW, 2.15 s, suite 1209/1209. Harness classify 2-subject sample:
75 probes in 0.6 s TOTAL (~8 ms/probe), missing=0 spurious=0.

BUT the full production classify (rerun12653.sh) now TIMES OUT both
modes at 420 s (previously answered unsoundly in 133/181 s): read-offs
are all fast (0.0–0.1 s, all NONDET, 36–44 candidates each); the wall
is the ~560 pairwise probes with a FEW pathological ones —
SLOW-PAIR profiling run in flight. Suspects: pairs where the at-most
actually fires (PathOfLengthK subjects: choose + nondet merge search)
and the 4 still-eager EM disjunctions. Next levers: (a) lazy/guarded
treatment for the EM pairs, (b) probe env reuse (task #13), (c) probe
ordering/budget.

## 2026-07-07 (cont-3) — wave 2 committed (2bb78d5); DDB wrong-root-cancel PINPOINTED to the u29 tracked line

Committed 2bb78d5 (all suite-green 1209): lazy triggered-OR +
KM_BRIDGE_DUMP_TOPGCI census + DETERMINISTIC successor order
(succ_role_hash HashMap iteration was per-process RANDOM — run-to-run
backtrack variance 155/723/1388 on identical probes; now sorted by
individual id, 3x identical) + merge-causing clash descriptors
(createIndividualMergeCausingDescriptors cpp 16690–16713 port: link +
contained-qualifier descriptors per counted successor, chained into the
at-most clash AND addBranchClashes'd onto the MERGE/QUALIFY decision
nodes' clash track points — the clash tp HEADS branch_track_points, so
get_collected_filtered_clashed_descriptors_from_branch reads it).

**THE REMAINING 12653 BLOCKER (deterministic 0.33 s repro)**:
`KM_HT_COW=1 KM_HT_DDB=1 KM_BRIDGE_PAIR=AlternativePath,PathOfLength2`
still wrongly ROOT-CANCELS (gold: AlternativePath ⊑ Path only). The
evidence chain (all via new dumps):
- FINAL-CLASH = ⊥/⊤ @ n1 via apply_bottom_rule; KM_BRIDGE_DUMP_DEP_CHAIN
  shows BOTH descriptors' dependency chains passing through
  `tp#115 node=Or nondet=true tag=4` — the clash IS branch-dependent.
- The root-cancel comes from the ALL-SIBLINGS-REFUTED propagation site
  (u29 backtrack_non_deterministic_branching_clashed_descriptor,
  cpp 7085–7349 port), NOT the entry-line site; its collected closure is
  a SINGLE descriptor `[c=546 det=true tag=0 tp=#112]` = the refuted
  decision's own cause (tp#112 = the TOP-attached GCI implication that
  introduced the disjunction). The siblings' stored clash sets
  contribute ZERO non-local causes — unchanged even after the
  merge-causing wave (byte-identical backtracks=71).
- So the loss is in the TRACKED-LINE STEPPING: the per-alternative mark
  (`tracked_clashed_descriptor_before_proc_tag_list` → set_clashes)
  stores an empty/local-only remainder — the descriptors that should
  carry the deeper decisions' taint (e.g. tp#115's Or) never make it
  into the alternative's stored closure. NEXT: side-by-side audit of
  backtrack_non_deterministic_branching_clashed_descriptor + the line
  stepping (u29/u30 create_tracked/step functions) against Konclude cpp
  7085–7349 / 6963–6974, with the 0.33 s repro + DDB-ROOT-CANCEL dump.

Verdict-mode matrix for 12653 pairwise probes as of 2bb78d5:
- no-COW no-DDB: light pairs CORRECT + fast (~8 ms–2 s); heavy pairs
  (at-most fires) thrash 54.8 s+/2.3 M backtracks, verdict unvalidated.
- COW no-DDB: sound restore but >300 s/pair — unusable.
- COW+DDB: 0.33 s BUT wrong root-cancel (the open bug). Fixing the
  tracked line makes this the production mode (sound + fast).
Also: 117 GB COW+DDB blowup earlier was PRE-lazy-OR (search itself
exploded); ws killed by PID per [[feedback_ws_no_orphans]].

## 2026-07-07 (cont-4) — DDB TAINT-LOSS ROOT CAUSE FIXED (2a869e8): DetLink back-edges were DETACHED

**THE u29 wrong-root-cancel root cause**: Konclude's one-back-edge
dependency nodes run `addAfterDependency(&mPrevLinkDep)` in their
CONSTRUCTORS (CMERGEDCONCEPT/CALL/CMERGEDLINK/CAUTOMATTRANSACTION/
CREPRESENTATIVE{ALL,JOIN}/CFUNCTIONAL-both-edges; VALUE/NEGVALUE/
NOMINAL/ROLEASSERTION/SAMEINDIVIDUALSMERGE/RESOLVEREPRESENTATIVE chain
conditionally at init) — the inline back-edge is a MEMBER of
additional_after. The port kept it as a detached `DetLink{prev}` field:
invisible to BOTH `depended_branching_tag` AND the u29
additional-dependency traversal → a MERGEDCONCEPT's merge-decision
taint vanished → branching tags under-computed → clash closures
decision-local → wrong ROOT-CANCEL. Fixed 2a869e8:
`bind_det_link_prev` (bind + chain, no-op on NONE tp) + all wrapper
sites; 3 shape tests updated (the old expectations ENCODED the bug:
continue-tp tag must be the max over BOTH back-edges). Diagnosis tools
that got there: DEP-CHAIN walker (both clash chains passed
`Or tp#115 nondet tag=4` while the analysis said det/tag-0),
DDB-ROOT-CANCEL[propagated] closure dump (single `[c=546 tag=0
tp=#112]` descriptor = the decision's own cause).

Effect: wrong root-cancel GONE; Property ⊑ Path CORRECT under COW+DDB.
Also fixed en route: run-to-run search nondeterminism (succ_role_hash
HashMap iteration → sorted by individual id, 2bb78d5).

**LESSON (40ce66d): lazy covering-OR is INCOMPLETE** — deferring
trigger-less atomic-operand disjunctions breaks case-split entailments
(A ⊑ B ⊔ C, both branches close ⇒ A ⊑ D needs the branch); the suite
caught it (3 disjunction tests). The at-most defer is different in
kind: the deferred disjunct is structurally CHECKED (pessimistic count)
and link-events re-check it. EM-pair branching reduction needs real
absorption complementarity analysis, NOT a defer.

**12653 heavy pairs post-fix = throughput/memory wall, 3 measured holes**
(1d188d6 threads KM_BRIDGE_PROBE_BUDGET_S into the drive + saturation
loops as `algo.drive_deadline`; suite green):
1. Something OUTSIDE both checked loops still runs unbounded on heavy
   probes (126 GB / 10 min despite 1-s budgets). PRIME SUSPECT: the u29
   analysis itself — `append_tracked_clash_chain` walks to chain end =
   O(n) per append ⇒ QUADRATIC clash-set growth across 100k+ backtracks
   (time AND memory); needs tail-pointer or set-based accumulation +
   its own deadline check.
2. ~300 MB RESIDENT PER PROBE across the classify (fresh ctx3 per
   probe never returns memory — leak or allocator retention;
   MALLOC_ARENA_MAX=2 did not help). Task #13 env/databox reuse fixes
   cost AND retention.
3. Even sound+fast probes need the search to converge; profile
   (KM_BRIDGE_PROGRESS): nodes 20-35 but bp_depth ~150, ddb_jumps ==
   drives, fallbacks=0, 46 M inserts/120 s — DDB works but re-explores
   isomorphic subtrees; Konclude wins here via absorption + unsat
   caching (both unported).
WS SAFETY: four near-OOM kills this session (117/74/126/126 GB) — do
NOT run 12653 heavy-pair probes on ws without a hard RSS cap wrapper;
kill by PID immediately at >80 GB.

## 2026-07-07 (cont-5) — 12653 harness classify SOUND end-to-end (42a8b74)

The 126 GB stall was the READ-OFF path: bridged_classify_subject had NO
deadline (pre-taint-fix its heavy subjects only LOOKED fast because
wrong root-cancels cut them short). 42a8b74 sets algo.drive_deadline
there from KM_BRIDGE_PROBE_BUDGET_S (STOP → verdict None → no
derivations for the subject; sound).

**RESULT (ws, COW+DDB + RECOG, all 10 gold subjects)**:
- budget 2 s/probe: **46.7 s, spurious=0, missing=2** (memory bounded,
  run completes cleanly). The whole spurious family (was 11 no-DDB /
  39 DDB) is GONE.
- budget 10 s: 79.8 s, SAME 2 missing — the pairs don't converge with
  more budget.
- missing = PathOfLength3/4 ⊑ Path: unsat proofs that must EXHAUST the
  at-most/choose/merge × EM-covering case space (the search DDB
  re-explores isomorphically). These need the NEXT BIG PIECE —
  absorption complementarity and/or unsat caching and/or the Konclude
  saturation pre-stage — NOT budget/discipline tweaks (proven).

Production impact: the bridge can now answer 12653 SOUNDLY but
INCOMPLETELY (2 pairs) — production classify requires complete
answers, so 12653 stays unsolved-but-sound until the completeness arc;
the at-most/DDB machinery repairs (2a869e8 etc.) benefit every bridged
ontology.

## 2026-07-07 (cont-6, dbfbe4a) — the 2 missing pairs: full causal chain + the ONE remaining u29 bug

Why PathOfLength3/4 ⊑ Path stay missing: their SUBJECT READ-OFF (a SAT
search) STOPs on budget → the harness skips ALL pairwise probes for the
subject (SUBJ ... STOP → no candidates). The read-off thrash mechanism,
MEASURED via new diagnostics (ddb_already_marked_count 1:1 with
fallbacks; DDB-ALREADY-MARKED in_stack=true current_alt=true
remaining=false, always the SAME tp): every clash re-traces to one
already-marked EXHAUSTED mid-stack alternative; the analysis early-outs
on the stale mark; chronological fallback keeps searching INSIDE the
refuted subtree. Konclude never sees this (branch-task cancellation
kills refuted subtrees).

THE ESCAPE (u02 scan case: current-alt marked + exhausted → discard
through the decision, retry backtrack below) collapses the thrash —
PathOfLength3 read-off 120 s/2.9 M backtracks → **10.5 s** — but then
the search reaches the STILL-BUGGY u29 all-siblings-refuted propagation
(backtrack_non_deterministic_branching_clashed_descriptor): its
collected closure degenerates to the decision's own tag-0 cause
(`[c=546 det=true tag=0]` — the SAME signature as the pre-2a869e8 bug)
→ wrong root-cancel → 12 spurious PathOfLength3 pairs. The loss is in
the BEFORE-PROC-TAG REMAINDER stepping
(get_backtracked_deterministic_clashed_descriptors_before_processing_tag
+ what gets set_clashes'd per alternative) vs Konclude cpp 7677–7776 —
note cpp 7686's INVARIANT (no nondet descriptor processed after the
max-branching-level decision) which the in-process port may violate.
Escape gated OFF by default: KM_HT_DDB_REFUTED_DISCARD (the fast
deterministic repro NEEDS it: KM_HT_COW=1 KM_HT_DDB=1
KM_HT_DDB_REFUTED_DISCARD=1 KM_BRIDGE_PAIR=PathOfLength3,AlternativePath
→ spurious pairwise=true in seconds, DDB-ROOT-CANCEL[propagated] dump).

ALSO fixed (dbfbe4a): harness classify loops (subject + pairwise) never
threaded Bridged.singleton_concepts (probe harness + production
fresh_bridge_env did) — value-identity merges were silently OFF in the
gold-measurement loops.

DEFAULT-MODE STATE (ws, COW+DDB, 30 s budget): full 12653 classify
**missing=2 spurious=0 in 160.7 s**, memory bounded, suite 1209/1209.
THE ONE FIX that closes 12653: the u29 before-proc-tag remainder — then
the refuted-discard default-ons, read-offs converge (10.5 s measured),
and the classify should go missing=0 spurious=0.

## 2026-07-07 (cont-7, 43bfff3) — u29 wrong-root-cancel REFINED: context-dependent sibling marks

New SIBLING dump at the propagated root-cancel (43bfff3) + dep-chain
walk on the repro:
- the ⊥'s chain DOES pass properly-tagged nondet Merge decisions
  (tags 107–111) — the DetLink/merge taint machinery WORKS;
- but the refuted covering decision's two sibling remainders contain
  ONLY tag-0 descriptors (real derived concepts whose chains bottom at
  the base) → union level 0 → root-cancel. SIBLING[2] = the decision's
  own clash track point (heads branch_track_points, pre-marked, EMPTY
  for OR decisions — Konclude cpp 16914 attaches planOR's
  contained-negated-disjunct clashes there; port may miss that).
- **INTERNAL INCONSISTENCY PROOF (no gold needed)**: the same run's
  read-off finds a MODEL for PathOfLength3 (SAT 10.5 s) while pairwise
  declares PathOfLength3 ⊓ ¬X unsat for a dozen unrelated X — the
  propagated root-cancel is definitively wrong.
- MECHANISM (refined): the two siblings were marked at DIFFERENT times
  under DIFFERENT surrounding contexts; marks persist
  (watermark-exempt). At least one refutation had a CONTEXT dependency
  its recorded closure missed — some derivation on the clash node whose
  chain reads tag-0 but is branch-dependent in fact. AUDIT ORDER for
  the taint hole: (1) edge-installed domain/range + universal
  reapplication along MERGE-RELOCATED links (ht_relocate under alt tp —
  but re-derivations after rollback?), (2) apply_or_rule's
  deterministic one-open-disjunct path (planOR contained/secondNot
  arms — under which tp does the surviving disjunct get added?),
  (3) the lazy-OR role-reapply re-fire tp, (4) COW rollback
  re-derivation: after pop_branch_epoch, re-derived concepts in the
  NEXT alternative may reuse... (epoch-exempt con_descs? — con_descs
  ARE epoch-exempt: a label-map journal restores the MAP, but could a
  restored map entry point at a descriptor whose dep tp belongs to the
  POPPED alternative? "persistence cannot leak popped concepts back
  into a restored label" per the epoch note — re-audit that claim for
  REAPPLY-derived entries).
Repro (seconds): KM_HT_COW=1 KM_HT_DDB=1 KM_HT_DDB_REFUTED_DISCARD=1
KM_BRIDGE_PAIR=PathOfLength3,AlternativePath + KM_BRIDGE_DUMP_CLASH=1
KM_BRIDGE_DUMP_DEP_CHAIN=1 (SIBLING + chain dumps).

## 2026-07-07 (cont-8, d847cb5) — taint lie NARROWED to an implication-fire dependency recording

The SIBLING late-desc chain walk (d847cb5) shows the stored remainders'
chains are SELF-CONSISTENTLY deterministic (Implication ← Connection ←
… ← IndependentBase, tag 0 throughout, e.g. c=45@tp#93594). But the
same run's READ-OFF MODEL for PathOfLength3 refutes the claim: a truly
deterministic refutation chain fires in EVERY branch including the
model branch — and the model exists. ⇒ some implication firing records
a WRONG dependency (an early/implication-own tp instead of the true —
branch-dependent — trigger). Audit findings so far: one-open-disjunct
OR path ABSENT in the port (always branches — over-taints, sound);
create_oronly_option_dependency has NO callers; merge taint OK (chains
show Merge nondet tags 107–111); domain/range + ∀-reapply thread edge
tps.

**NEXT (the concrete fix hunt)**: audit the REAPPLY-driven implication
fire path — when a trigger concept ARRIVES later and the condensed
reapply queue re-processes the implication (u09 trigger scan / u10
reapply consumption / u36 insert-reapply iterator), which tp does the
created CONNECTION dependency record? Compare against Konclude's
CCondensedReapplyQueue → implication triggering (the 93e62e4 fix
covered the direct trigger-scan path; the reapply path may still
default to a stale descriptor's tp). The lying chains' shape:
`Implication ← Connection ← (EARLY tp #110/#84) (+And siblings)` —
find the fire site that records those early tps for late firings.
After the fix: rerun the repro (expect no root-cancel → pairwise=false
for PathOfLength3 vs AlternativePath), suite, then classify with
KM_HT_DDB_REFUTED_DISCARD=1 (expect missing=0 spurious=0), then
default-on the discard, production wiring (#14), IBEX panel.

## 2026-07-07 (cont-9) — REDIAGNOSIS: it is a DETERMINISTIC KERNEL/ENCODING bug in the DATATYPE-VALUE machinery, NOT a DDB bug

Two corrections to cont-7/8:
1. **My internal-inconsistency proof had a hole**: the probe's
   "deterministic" facts INCLUDE the ¬sup seed (base-level in the probe
   but absent from the read-off) — so a deterministic probe-refutation
   is consistent with subject-SAT. The u29 analysis + chains may be
   HONEST.
2. **Gold arbitration**: Konclude's own sig
   (/tmp/konclude__ore_ont_12653.owl.sig.gz) says PathOfLength3 ⊑ Path
   ONLY ⇒ the pairwise unsat verdicts (PathOfLength3 ⊑
   AlternativePath/Universe/...) ARE spurious ⇒ since the chains
   honestly record kernel derivations, the KERNEL DERIVES A
   DETERMINISTIC REFUTATION KONCLUDE WOULDN'T — a rule/encoding bug on
   the deterministic path, reachable without DDB (DDB just finds it
   fast via the refuted-discard).
3. u09 implication fire path re-audited AIRTIGHT (trigger CONNECTION
   deps built on re-fires too; the reapply path IS the same function).
   One-open-disjunct OR path absent (always branches — over-taints).

**THE ACTORS (KM_BRIDGE_TAG_NAMES decode of the refutation closures)**:
c17=__dt__integer (the repeated ¬17-vs-17 clash family!),
c56=__dt__val__"3"^^xsd:integer, c45/41=__slot__f_Q_42_{2,0} (slots of
Q_42 = the PathOfLength3 ≥3-definer), c13/15=__slot__f_Q_10_{0,1}
(slots of Q_10 = PathOfLength2), c12=PathElement, c10=Q_10, c26=Path;
c546/423/411/882/552/903/419 = built (or_of/atmost) concepts. The
wrong deterministic refutation runs through the DATATYPE VALUE + SLOT
machinery: __dt__integer/¬__dt__integer clashes on (likely MERGED)
value/slot nodes — suspicion set: (a) the singleton value-identity
merge (d58c2b2) merging val-"3" carriers across semantic positions and
dragging slot/dt constraints together, (b) functional/at-most DATA-role
merging combining distinct-value nodes, (c) the frontend/cb_to_ht
encoding of negated value restrictions (¬(length=k) → where does
¬__dt__integer come from?). NEXT: KM_HT_NO_SINGLETON A/B on the repro
pair (if pairwise flips to false → the singleton merge is the bug);
then KM_HT_BRIDGE_RECOG off A/B; then trace the FIRST ¬__dt__integer
derivation (KM_BRIDGE_WATCH_NEGTAG=17 + backtrace).

**A/B RESULTS (decisive)**: KM_HT_NO_SINGLETON=1 → STILL spurious
(singleton merge EXONERATED). KM_HT_BRIDGE_RECOG unset → pairwise=false
CORRECT. ⇒ **the deterministic spurious refutation is IN THE RECOG
ARM**: either the ≥k-recognition encoding in bridge.rs (audit: the
hub-vs-target ORIENTATION detection incl. the inverse-orientation
branch `inv_roles[r0]`; GUARD polarity in `b.implication(head,
&triggers)`; the qual single-operand restriction) or the at-most/
choose/merge machinery the encoded ≤(k−1) activates on DATATYPE SLOT
successors (¬__dt__integer derivations — note my choose rule's ≤0 path
adds ¬C deterministically; ¬(≥1 f.dt) ⇒ ≤0 f.dt is a legitimate
¬dt_integer source IF the ¬≥1 itself is right). NEXT SESSION: (1)
KM_BRIDGE_WATCH_NEGTAG=17 backtrace of the FIRST ¬__dt__integer on the
repro (which rule/clause derives it), (2) side-by-side the RECOG
encoder's orientation/guard handling vs the raw clauses
(KM_BRIDGE_DUMP_RECOG prints every recognized clause), (3) synthetic
unit test of the suspect shape per [[feedback_build_before_benchmark]].
Repro (~seconds, deterministic): KM_HT_COW=1 KM_HT_DDB=1
KM_HT_DDB_REFUTED_DISCARD=1 KM_HT_BRIDGE_RECOG=1
KM_BRIDGE_PAIR=PathOfLength3,AlternativePath.

## 2026-07-07 (cont-10, FINAL narrowing) — the driving at-most PINNED: `Q_13 ⊑ ≤1 r1.__dt__integer`

WATCH-NEGTAG=17: every ¬__dt__integer add comes from
ht_apply_atmost_merge's CHOOSE paths. New KM_BRIDGE_WATCH_ATMOST
(committed): the driving at-most = **concept 882 = ≤1 role_101
(TInput role idx 1) . __dt__integer, cardinality=1, negate=false,
firing on the PROBE ROOT n0 with dep_tag=0 (deterministic!)**,
choosing over f-successors n1/n5/n11 (the slot/value nodes), then on
n1→n16 (dep_tag=36). Source clause per RECOG dump: `RECOG r=1 k=2
qual=Some(7=__dt__integer) guards=[(129,false)] (absorbed)` and
**guard idx129 = tag139 = Q_13** (a definer). So the source clause is
`Q_13(x) ∧ dt(y1) ∧ dt(y2) ∧ r1(x,y1) ∧ r1(x,y2) → y1=y2` — encoding
EXACT (`Q_13 ⊑ ≤1 r1.dt_integer`).

**THE REMAINING QUESTION (one level up)**: why does Q_13 hold
DETERMINISTICALLY on n0 (= PathOfLength3 ⊓ ¬AlternativePath) while n0
also deterministically gets ≥2 r1-successors that can each become
dt_integer? Under Konclude this configuration is SAT — so either (a)
the Q_13 derivation on n0 is an over-derivation (trace its chain:
KM_BRIDGE_WATCH_TAG=139), (b) the slot successors should not all be
r1-successors (frontend/cb_to_ht role collapse?), or (c) the choose/
merge handling of DATA successors diverges from the CB engine's
concrete-domain oracle semantics for eq-heads on VALUE variables
(bridge realizes value-eq as NODE MERGE; slot disjointness then
clashes where the oracle would only equate VALUES — check whether the
original clause's y-vars denote VALUES (oracle) vs NODES (merge): if
the clausal eq is over DATA-VALUE terms, node-merging slot nodes that
carry DIFFERENT slot markers over-clashes = THE SUSPECTED SEMANTIC
MISMATCH; Konclude's databox treats value equality without merging
tableau nodes). Next: KM_BRIDGE_WATCH_TAG=139 chain; inspect the
frontend clause (dump_clauses --canon laptop-safe) for the r1/slot
structure; decide (a)/(b)/(c); synthetic test; fix.

FINAL data points (cont-10 close): role idx1 = **hasLength** (no role
collapse — hypothesis (b) DEAD; KM_BRIDGE_ROLE_NAMES env added). The
at-most = `Q_13 ⊑ ≤1 hasLength.integer` — natural ontology semantics
(functional-on-integers hasLength). Q_13 lands on n0 via a plain
DETERMINISTIC u09 implication fire (WATCH_TAG=139: u09
apply_implication_rule ← tableau_rule_choice). So the decision is
between (a) the absorbed implication chain deriving Q_13 on
PathOfLength3-roots being an over-derivation (identify the source
clause: extend WATCH-IMPL to print ops for head=139, or read the
absorbed chain from the clauses), and (c) the ROOT having ≥2
hasLength successors whose value-eq the bridge resolves by NODE MERGE
where the CB oracle equates VALUES only. Note the choose fired over
THREE hasLength successors of n0 (n1/n5/n11) — find who creates the
2nd/3rd hasLength edges (KM_BRIDGE_DUMP_EDGES needs KM_BRIDGE_TRACE
and sits on the classify-subject path, not the probe path — move it or
use WATCH on the edge-install). The 2nd/3rd hasLength successors are
the anomaly: PathOfLength3 needs ONE. Whoever creates them (Q_10/Q_42
definer content firing on the ROOT because RECOG derived Q_10/Q_42
there — legitimate per the clauses — each with their OWN
∃hasLength.val_k content) → then ≤1 hasLength.integer forces merging
val2/val3 nodes → slot/value disjointness clash → the spurious unsat.
If THAT is the story, the CLAUSES genuinely entail the clash unless
the CB treats the value-eq head differently (oracle) — decide by
checking what the CB's eq-head handling does with data-value vars
(engine.rs Eq rules + the pairwise concrete-domain oracle 1e168e4)
and whether TInput carries val_j⊓val_k⊑⊥ clauses.

**RESOLVED (cont-10 close)**: frontend/datatypes.rs EMITS pairwise
value disjointness AS CLAUSES (`__dt__val__v(x) ∧ __dt__val__w(x) →
⊥`, "value clash v ≠ w") plus membership/covers — the clausal
semantics already contains value conflicts, so the bridge's node-merge
realization of value-eq FOLLOWS the clauses (strong-(c) DEAD). ⇒ if
the spurious refutation is clause-entailed (to be verified), the
defect is in the FRONTEND/NORMALIZATION clause generation for 12653 —
the RECOG clauses themselves are standard (≥k ⊑ Q_k recognition of ≡
decompositions); the suspect is EXTRA hasLength existentials imported
via definer CONTENT (which definer clause gives the root its 2nd/3rd
hasLength successors — Q_10/Q_42/Q_9 content?).

**NEXT-SESSION ENTRY POINT (one concrete step)**: dump the TInput
clauses referencing concept idx 129 (Q_13) / idx 7 (__dt__integer) /
role idx 1 (hasLength) — 10-line addition to the bridge test (iterate
env.tin.clauses, print any clause whose atoms mention those indices,
formatted like the UNSUP dumper) — then hand-verify the entailment
chain `PathOfLength3 ⊓ ¬AlternativePath ⊢? ⊥` at the clause level
against the OWL axioms (ore_ont_12653.owl on ws /tmp). If
clause-entailed → frontend normalization bug (fix in
normalise/preprocess, then byte-identity revalidation per CLAUDE.md
frontend rules + full-corpus check); if NOT clause-entailed → the
kernel derives it wrongly and the derivation trace (WATCH envs) finds
the bad rule. Either way 12653 then goes gold-clean, the
refuted-discard default-ons (read-offs 10.5 s), production wiring
(#14), IBEX panel.

## 2026-07-07 (cont-11, SESSION END) — clause dumps done; the endgame is ONE disjointness-pattern check

KM_BRIDGE_GREP_CLAUSES=<c:IDX|r:IDX> landed (bridge probe test).
Dumps established:
- hasLength family CLEAN: Q_12 ≡ ∃hasLength.integer, Q_40/45/50 ≡
  ∃hasLength.val2/3/4 (both directions), Q_13 = the functional guard
  (Q_11 ≡ Q_12 ⊓ Q_13), `Q_13 ∧ dt(1) ∧ dt(2) ∧ hasLength ×2 →
  eq(1,2)`.
- Q_10 family: Path ⊑ Q_10; Q_10 ⊑ ∃hasPathElement.def_exfil_f_Q_10_{0,1};
  Q_37 ≡ Q_10 ⊓ Q_38; PathOfLength2 ≡ Q_37; PathOfLength2 ≡ Q_40 —
  and the OWL CONFIRMS both equivalences (ObjectExactCardinality(2
  hasPathElement PathElement) AND DataHasValue(hasLength,"2")) — the
  frontend is FAITHFUL here.
- HAND-DERIVATION: on the probe root (=3 distinct elements from
  PathOfLength3), the EM pair Q_38(≤2)∨Q_39(≥3): Q_38-branch dies
  LEGITIMATELY (≥3-distinct vs ≤2); the Q_39-branch MUST survive
  (Konclude SAT) — its wrongful death is the bug. Q_39's ∃-slot
  content adds 3 NEW def-filler element successors (some-rule can't
  reuse: existing successors lack the Q_39-def fillers) → 6 element
  successors under the =3's ≤3 side → needs a 3-cross-merge matching.
**THE DECIDING CHECK (next session, one dump)**: the def-filler
disjointness pattern — `KM_BRIDGE_GREP_CLAUSES` on the def_exfil/slot
indices of Q_39-vs-Q_42/PathOfLength3 groups. If the frontend emits
`def_a(y) ∧ def_b(y) → ⊥` ACROSS ∃-groups (not just within a ≥k
group), the 6→3 matching is clausally impossible → the CLAUSE SET
entails the spurious refutation → FRONTEND BUG (definer-disjointness
scoping in normalise/preprocess; fix + byte-identity + corpus
revalidation). If disjointness is per-group only → KERNEL merge/search
bug killing a feasible matching (trace the Q_39-branch death with the
WATCH envs). Then: 12653 gold-clean → discard default-on → #14 →
IBEX panel.

## 2026-07-07 (cont-12, 72d68de) — SYNTHETIC ORACLE LANDED; **COW EPOCH RESTORE is the broken layer** (DDB exonerated)

`covering_atmost_cross_merge_sat` (#[ignore], bridge.rs): 20-line OFN
miniature of the 12653 structure; X satisfiable via the B-branch 6→3
cross-group merge matching. TOGGLE MATRIX (deterministic, 0.03–1.5 s):
plain PASS; **KM_HT_DDB=1 PASS (DDB itself exonerated!)**;
**KM_HT_COW=1 FAIL (41 750 backtracks, EXHAUSTION — root_cancelled=
false!)**; COW+DDB FAIL (10 699). ⇒ the branch-epoch COW restore
LOSES LIVE ALTERNATIVES (every alternative spuriously clashes after
rollbacks); the u29 root-cancel was a downstream symptom of analyzing
already-corrupted searches. Complementary: 12653 classify DDB-only =
spurious=2 missing=2, 63.6 s (the OLD no-COW leftover leak family
AlternativePath/MainPath ⊑ PathOfLength2 returns). SO: no-COW leaks
refuted-alternative derivations INTO siblings; COW corrupts state
ACROSS rollbacks — ONE COW fix solves both modes' soundness.

**CORRECTION (03866ba)**: the dangling-satellite INVARIANT IS CLEAN
(ht_check_dangling_satellites after every pop: zero out-of-range
label-set/queue/succ-hash ids). So the out-of-range theory is
disproven; remaining: (a) WITHIN-RANGE aliasing (truncated+reallocated
slot read via surviving id — needs an OWNER-identity check: add a
debug owner-node field to ReapplyConceptLabelSet), (b) arena-index
GENERATION-REUSE explains the 'n3 label changed' reading (different
node generations at index 3 across pops — log nodes.len() per event
to confirm). THE HARD ANOMALY THAT REMAINS: both e-generations
coexist as SIMULTANEOUS root successors in ONE at-most gather
(succs=[1,2,4]: gen-1 n1/n2 + gen-2 n4) — the root's succ-role-hash
holds links to both generations at once ⇒ the ∃s re-fired in a state
where gen-1 lacked their DEF fillers or hash entries ⇒ trace the ∃
re-fire moment (log apply_some_rule's already-exists check verdict +
the state of the gen-1 nodes' labels at that moment, SEARCH_LOG-gated
in apply_some_rule when already_exist==NONE and a same-filler
successor... just log every CREATE with parent+filler+existing-succ
labels). NOTE the root's succ-hash is DATABOX-adjacent state via
node.use_succ_role_hash → journaled arena — but check the
`node_reapply_role_successor_hash` LAZY REALLOC pattern (steals prev
content into a NEW allocation) interacting with epochs: field
restored on pop, content restored, new alloc truncated — verify
empirically with the create-log.

**COW BUG DECIDED (7868f5c)**: the anomalous firings are am=120 (the
A-content ≤2) over **DUPLICATED e-group successors** — n4/n5/n6 carry
the SAME fillers E1/E2/E3 as n1/n2/n3 (the ∃s re-fired despite
existing successors), and **n3's label CHANGES IDENTITY across
states** ([1,21,33] vs [1,15,33]) — the fingerprint of a
**dangling/reallocated LABEL-SET id after epoch truncation**: a
pre-epoch node whose label-set slot was allocated (or replaced) inside
a later epoch survives the pop pointing at a truncated slot → label
reads empty (∃ already-exists check fails → duplicate successors →
phantom at-most violations → exhaustion) or aliases a reallocated slot
(foreign labels). FIX LOCUS: node.use_reapply_con_label_set lifecycle
vs the label_sets epoch journal — options: (a) ensure the node's
label-set-id FIELD write is reliably journaled (nodes arena
get_mut_journaled coverage — check `node_reapply_concept_label_set`'s
lazy-allocation path and any direct field writes), (b) allocate node
label-sets in the NODE's creation epoch, (c) validate/refresh dangling
satellite ids after pop. Same hazard class for ALL node satellite ids
(queues, distinct hashes, succ-role hashes, reapply hashes) — audit
the lazy `node_*(node, true)` allocators. ONE inspection round
completes the fix; oracle 0.03 s validates; then the whole cascade
(suite → 12653 classify → discard re-eval → #14 → IBEX panel).

**FINAL NARROWING (d46bc88, atmost-pairs verdicts)**: the search DOES
enumerate and try all pair alternatives (in-group e-pairs correctly
die on filler-disjointness ⊥ — the A-branch ≤2 refutation over
succs=[1,2,3] is CORRECT and mergeability verdicts are all 'ok' since
the label-clash check only blocks same-tag-opposite-polarity). **THE
ANOMALY**: the ≤2 at-most (A-branch CONTENT) ALSO fires in states
`succs=[1,2,4] / [1,2,5] / [1,3,4] / …` — B-branch/d-group successors
coexisting with the A-restriction, impossible under correct covering
alternation. Two candidate mechanisms: (i) the ≤2 DESCRIPTOR LINGERS
across the covering's COW advance (the label restore removes A and
its AND-content, but a REAPPLY-QUEUE or PROCESSING-QUEUE copy of the
≤2 con-proc-desc re-fires it inside the B-branch — check what happens
to a QUEUED/REAPPLY-REGISTERED descriptor whose label entry was
rolled back: the queue journals restore push-time queues, but the ≤2
was queued/registered UNDER the A-alternative — pop should remove it;
UNLESS the reapply registration was made under is_concept_reapplied
guard semantics that survive), or (ii) rolled-back/merged-away nodes
REAPPEARING as root successors (n4/n5/n6 identity unknown). NEXT (one
run): extend the atmost-pairs log with the at-most's OWN concept tag +
bound + each successor's compact label → identifies which at-most and
what n4/n5/n6 are → the fix follows directly. All instrumentation
committed (d46bc88); oracle repro seconds.

**REFINED AGAIN (eeb4d19)**: the epoch/branch alignment check is CLEAN
(rollback targets the correct push point) and the label diff shows
PLAIN's extra concepts are LEFTOVERS (plain finds its model in
leftover-polluted state — its pass is partly luck); COW's post-restore
label IS the faithful push-time state. ⇒ the bug is NOT the restore:
under CORRECT restore the search EXHAUSTS a satisfiable space — a
COMPLETENESS defect in the post-rollback machinery. All clashes =
choose-¬E vs (re-)derived E. TOP SUSPECTS: (a) post-rollback
re-derivation/reapply coherence — a successor's E rolled back with the
queue entry that derived it already consumed pre-push?? (both label
and queue restore to push-time — coherent in principle; audit what
RE-derives E when it was derived pre-push... then it's IN the restored
label — so the dying paths need E arriving POST-push and the choose
firing BEFORE the re-derivation: ORDER of the restored queue vs the
choose's reapply-driven at-most re-fire), (b) the at-most re-fire
protocol after rollback (re-gather sees rolled-back state; pending
re-derivations change counts later; the reapply registration may have
been rolled back with no re-registration → at-most never re-checks →
or the choose fires on temporarily-undecided successors and its ¬E
lingers... but ¬E is under the choose ALT TP — backtrackable ✓).
NEXT: 60-event label trace of ONE full subtree exhaustion under COW
(bump KM_BRIDGE_SEARCH_LOG, read where every E-positive/merge path
dies); the smoking pattern will be either a choose firing that plain
never makes (order) or a merge re-check miscounting after rollback.

**COW divergence LOCALIZED (473ca41, KM_BRIDGE_SEARCH_LOG)**: plain
finds the model in 9 search events; COW's trace is IDENTICAL through
the shared prefix then the SAME decisions clash on DIFFERENT NODES
(3rd clash: plain `E/¬E@n1` vs COW `E/¬E@n2`) and COW exhausts. Every
clash = the CHOOSE rule's ¬E (qualifier alternative 0) vs derived E
(e_i ⊑ E / d_i ⊑ E). Under COW even the all-E + merge-matching paths
clash ⇒ the post-restore label/queue state after an OR-advance differs
from plain's snapshot-restore in a way that forces wrong ¬E choices or
kills the E-paths. File-based repro: ws:/tmp/mini_cow.ofn
(bridge_probe_pair X,Y — TAG_NAMES works; 33=E, 31/32/34=Q_10/11/12).
NEXT CONCRETE STEP: extend the advance log with the advanced node's
LABEL after restore (compact tag list) and diff plain-vs-COW per event
(~15 events total) — the first label difference IS the corrupted
structure; then fix pop_branch_epoch (or the advance path) for that
structure. Note: choose/merge BPs use epochs in BOTH modes (they pass
in plain), so the corruption is specific to the OR-advance epoch cycle
(pop+push on Disjunction BPs) vs the label/queue snapshot restore.

**COW-corruption suspects (next session, use the 0.03 s COW-only
repro)**: (1) algo/ctx-CACHED arena ids — the CompletionTaskHandle
Algorithm caches queue ids (processing_queue, immediate, depth, …) and
ctx caches (current node, label-set ids?); pop_epoch TRUNCATES arenas
then the next alternative re-allocates the same indices → cached ids
ALIAS different objects (queue corruption → nodes unprocessed/wrong).
Databox IS snapshot-restored (databox_epoch_stack full clone —
completion/context.rs push/pop_branch_epoch), so id→node redirects
restore ✓. (2) epoch-EXEMPT structures written under alternatives
whose content references TRUNCATED arena slots (con_proc_descs are
journaled; clash_descs/track_points/dep spine exempt by design). (3)
node fields mutated in place that the `nodes` journal misses (e.g.
fields behind satellite ids). Verdict-path tags landed:
KM_BRIDGE_TRACE2 → UNSAT-EXIT seed-insert / pass=N / probe-clash
(prints ddb/cow/root_cancelled/backtracks). Fix plan: reproduce →
instrument arena lens/cached ids across one pop/push cycle → align
with Konclude's task-fork semantics (fresh task = fresh caches!) —
likely fix = RESET the algo/ctx cached ids on pop_branch_epoch (the
in-process analog of task-fork cache initialization).

**VERDICT (cont-11 close, dump done)**: slot disjointness is
WITHIN-GROUP ONLY (`__slot__f_Q_10_0 ⊓ __slot__f_Q_10_1 → ⊥`; slots
are per-∃-group definers, `def_exfil_f_X_i → __slot__f_X_i`);
Q_38/Q_39 are a true complement pair (`⊤ ⊑ Q_38 ∨ Q_39`,
`Q_38 ⊓ Q_39 ⊑ ⊥` — EMELIM candidate that survived!); Q_38's ≤2 is
the GUARDED eq-recognition (fires on 3 known elements); Q_39 ⊑ 3
fresh-def ∃s. ⇒ cross-group merges clausally permitted ⇒ the 6→3
matching EXISTS ⇒ **the clause set does NOT entail the refutation ⇒
KERNEL BUG confirmed as the final locus**. Mechanism: the at-most
merge search over the 6 element successors — in-group pairings die on
slot-⊥ AFTER merging (label clash-set does NOT pre-block different
positive tags; the ⊥-clause fires post-merge → backtrack → try
another pairing via the nondet merge branching), feasible cross
pairings exist — but the u29 propagation (all-siblings-refuted) reads
the pairing deaths' remainders as DETERMINISTIC-only and root-cancels
(the cont-7..9 wrong-root-cancel, now with complete semantic
understanding of WHY the alternatives die and WHY at least one must
survive). NEXT-SESSION DELIVERABLE (per
[[feedback_build_before_benchmark]]): a SMALL SYNTHETIC unit test —
`⊤ ⊑ A ∨ B; A ⊓ B ⊑ ⊥; A ⊑ (guarded ≤2 R.E via eq-recognition);
B ⊑ ∃R.d1 ⊓ ∃R.d2 ⊓ ∃R.d3 (d_i pairwise ⊥, d_i ⊑ E); seed X ⊑
∃R.e1 ⊓ ∃R.e2 ⊓ ∃R.e3 (e_i pairwise ⊥, e_i ⊑ E) ⊓ (guarded ≤3 R.E)`
— probe X-satisfiability under COW+DDB+REFUTED_DISCARD: expect SAT;
the port presumably wrongly root-cancels → then fix the u29
before-proc-tag remainder / sibling-mark contexts against Konclude
cpp 7085–7349 WITH the failing test as the oracle. Then 12653
gold-clean → discard default-on → #14 → IBEX panel.

## cont-13 (2026-07-07): oracle ROOT-CAUSED — phantom card-def on the probe root (NOT the COW machinery)

The COW-only oracle failure (`covering_atmost_cross_merge_sat`) is a
BRIDGE TRANSLATION bug, not an epoch-restore bug. Chain of evidence
(each step one instrumented run on ws):

1. `atmost-pairs am=120` (A's guarded ≤2) fired on node 0 in the
   B-branch while tag 120 was NOT in node 0's label (advance-label
   dumps) → phantom constraint kills the SAT branch → exhaustion →
   spurious UNSAT.
2. reapply-arm log: 120 armed with op=CCATMOST at branch-epoch depth
   0 — an arm that no pop ever removes; every later link re-fires the
   unasserted ≤2 in every branch.
3. Dispatch trace (`proc node= tag= op= depth=`): the probe driver
   re-seeds the FULL `bridged.tbox` on the root each pass
   (`seed_concept_on_queue` — QUEUE-ONLY, no label add; bridge.rs
   ~1103 and ~1538). Every tbox concept is dispatched on the root:
   CCIMPLs self-gate on their trigger linkers (harmless), but a raw
   CCATMOST/CCATLEAST enforces UNCONDITIONALLY. `card_defs` pushed
   their raw absorbed ≤n/≥n into `tbox` (bridge.rs:887) → every probe
   subject got every marker's number restriction.
4. PLAIN mode has the IDENTICAL depth-0 dispatch+arm (trace-verified)
   but passed the oracle by terminating SAT early mid-branch (its
   known leftover laxness) — plain was never a valid reference for
   this bug. COW made the poison lethal because complete-restore
   search actually explores the space the phantom ≤2 refutes.
5. FIX: card_defs are no longer tbox-pushed; delivery is
   absorption-only (marker CCSUB unfold ⇒ label-membership holds).
   All other tbox entries are implication-wrapped (self-gating) or
   genuinely universal (functional ≤1, also in top_gcis — kept).

Implications: (a) the "COW epoch-restore search bug" hypothesis
(duplicated ∃-generations, dangling ids) is DEAD — the duplicated
generations were the LEGITIMATE per-branch recreations, and the
mixed-generation gathers were driven by the phantom ≤2's merges;
(b) suspect the same phantom-≤n mechanism in the 12653 bridge runs
(spurious no-DDB families / missing=2) — re-measure 12653 after this
fix; (c) diagnosis instrumentation now env-gated in-tree under
KM_BRIDGE_SEARCH_LOG: rule-dispatch log w/ label membership (u03),
reapply-arm w/ label+op (u10), reapply-fire w/ tag_present (u10),
∃-CREATE w/ existing-successor labels (u08). Possible hardening
follow-up: label-membership guard at reapply-fire — faithful because
Konclude labels are monotone down a task lineage, queue entries exist
only in tasks whose label contains the armed concept.

### cont-13 addendum: post-fix state (84e38bf, pushed)

- Oracle green in ALL SIX mode combos: plain / DDB / COW / COW+DDB /
  DDB+REFUTED_DISCARD / COW+DDB+REFUTED_DISCARD (0.00-0.35s). The u29
  "wrong-root-cancel" oracle blocker was ALSO the phantom card-def —
  task #12's oracle target is clear.
- konclude_ht suite 1209/1209.
- 12653 bridge classify HONESTLY TIMES OUT post-fix (both modes,
  420s; also with KM_BRIDGE_PROBE_BUDGET_S=5): the pre-fix 133s
  answer rode the unsound pruning (11/39 spurious proved it).
  Structural gotchas found: (a) `bridged_classify` uses `?` on
  `bridged_classify_subject` — the FIRST budget-deferred subject
  declines the WHOLE classification and km falls back to CB (no
  per-subject defer); (b) worker stderr is swallowed by the km
  orchestrator, so KM_BRIDGE_PROGRESS/PAIR-START prints never
  surface from `km classify` — per-probe timing needs a library-level
  driver on ws, not the production binary.
- Honest 12653/541 throughput levers, in leverage order: (1) faithful
  `branchingMergingProcRest` state machine in u08 (the port re-runs
  the ENTIRE greedy at-most rule on every new link — admitted "sound
  superset" PORT-NOTE); (2) u29 DDB quality over merge-pair searches;
  (3) refuted-discard default-on; (4) per-probe env reuse (#13);
  (5) per-subject defer + arm-merge in the #14 production wiring.
- No production regression risk: KM_HT_BRIDGE is opt-in; the ORE
  panel paths (cb_to_ht HT arms, KM_HT_CARD) never used the tbox
  root re-seed.

## cont-14 (2026-07-07): post-fix 12653 measurement — plain GOLD-CLEAN, DDB defect isolated to u29 cancel

`bridge_classify_full` on the 12653 gold sample (10 subjects,
budget 5s/probe), all post-84e38bf:

| mode | missing | spurious | wall |
|------|---------|----------|------|
| plain | 0 | 0 | 41.8s |
| DDB | 2 | 2 | 13.1s |
| DDB+REFUTED_DISCARD | 0 | 4 | 17.3s |
| DDB+COW | 2 | 0 | 61.7s |

- PLAIN is now GOLD-CLEAN on the sample — the pre-fix 11-spurious
  no-DDB family was entirely the phantom card-def. Plain's 4
  SLOW-PAIRs (X vs PathOfLength2, 15k backtracks, budget-STOP) all
  sit on gold-NEGATIVE pairs, so defer = correct by default.
- DDB "missing" (PathOfLength3/4 ⊑ Path) is NOT a verdict bug: the
  pair probe resolves CORRECTLY in ~30s but plain needs 0.3s — a
  100x DDB slowdown on genuinely-UNSAT probes; classify's 5s budget
  STOPs it. DDB read-off also drops Path (readoff_has=false).
- DDB "spurious" (AlternativePath/MainPath ⊑ PathOfLength2) IS a
  soundness bug: wrong-UNSAT in 0.8s / 7.5k backtracks on a SAT
  space plain cannot even resolve in 120s. NOT semantic branching
  (KM_HT_NO_SEMB → identical 2+2). Both directions point at the u29
  cancel analysis: over-prunes surviving alternatives AND fails to
  focus real refutations.
- Reproducers + attack plan recorded in task #12. Next session
  starts from the 0.8s wrong-UNSAT probe with the DDB-ROOT-CANCEL
  dump instrumentation.
- km-level classify (KM_HT_BRIDGE=1) still 420s-times-out because
  bridged_classify `?`-declines on the FIRST budget-STOP subject and
  falls back to CB; with per-subject defer (#14) plain-mode would be
  gold-clean on what it answers.

## cont-15 (2026-07-07): u29 wrong-UNSAT — mechanism narrowed, port verified faithful at 3 layers

Reproducer (0.8s): KM_HT_DDB=1 pair AlternativePath⊑PathOfLength2 →
pairwise=true, WRONG (HermiT sig agrees with Konclude: not subsumed;
PathOfLength3/4⊑Path ARE in HermiT's sig → the DDB "missing" pairs
are real subsumptions and that half is purely the 100x slowdown).

Verdict path = cancellation_root_task: early 3-alt recognition
decision (tps #113/114/115 tag=4) all-siblings-refuted; TRUE
collected closure (pre-consumption dump — the old dump formatted
AFTER initialize_tracking_line consumed the chain and showed only the
head) = [546 det, ¬158 seed, Q_10 det, 552 det] ⇒ per recorded data
the refutation is deterministic+seed ⇒ cancel is "valid" given the
inputs, so the LIE is that one sibling subtree was wrongly EXHAUSTED
(model never explored), not the propagation arithmetic.

Ruled OUT this session (verified against Konclude source):
- isProcessedAfter strict > (matches),
- getCollectedFiltered... dedups against a FRESH local set (matches),
- before-proc-tag unwinds after-tag descriptors instead of dropping
  (matches); ALLDEDUP drops are legitimate within one tracking line,
- EMPTY sibling stores legitimate for sibling-dependent deaths,
- semantic branching (NO_SEMB identical 2+2),
- untracked single adds (NONE-TP-ADD = 0 on the reproducer).

Remaining suspects (ordered): (a) discard-above-marked/pop-unmarked
justified only if every mark's dependency closure is complete — a
non-add rule path (merge relocation, distinct-hash insert, edge
install) with an under-covering track point breaks it silently;
(b) inner at-most/choose alternative wrongly clashed;
(c) marks minted from leftover-tainted clashes before the
unrestored_advance_count guard trips.
NEXT: KM_HT_DDB_NO_SKIP diagnostic (chronological fallback instead of
any discard-above-marked) — spurious gone ⇒ (a); then per-discard
logging to find the lost branch. Diagnostics committed under
KM_BRIDGE_DUMP_CLASH (DDB-MARK / DDB-UNWIND-* / true closure).

### cont-15 addendum: blame-split LANDED — the walk, not the propagation

KM_HT_DDB_NO_SKIP (committed): u29 marking + root-cancel stay ON,
mark-driven discard/advance OFF (pure chronological). Reproducer
flips wrong-UNSAT(0.8s) → budget-STOP (correct-undecided, same as
plain). ⇒ The mark-driven stack-walk discards are what wrongly
exhaust the SAT subtree; the propagation arithmetic just reports it.
Root cause class: some rule path's dependency track point
under-covers its real premises (NOT plain adds — NONE-TP-ADD=0;
suspects: merge relocation writes, distinct-hash inserts, edge
installs, blocking-condition reads), so a clash traces past a live
branch point and the walk discards it. NEXT: per-discard logging
(bp node/kind/alts + driving closure) on the 0.8s reproducer →
identify the lost branch → identify the under-tracked rule → thread
its dependency (faithful to Konclude's applyX dependency calls).

## cont-16 (2026-07-08): u29 wrong-UNSAT ROOT-CAUSED + FIXED (7c521cb) — LEFTOVER POISONING

Task #12 CLOSED at the mechanism level. The u29/DDB wrong-UNSAT was never a
dependency-tracking gap: three port audits were right that the chains are
faithful. The defect is **leftover poisoning of the analysis input**:

1. When an Or alternative's subtree CREATES SUCCESSOR NODES, the advance's
   restore guard (`node_count == node_count_at_push`) blocks the single-node
   label-snapshot restore (`unrestored_advance_count += 1`) — the failed
   alternative's disjunct and its derivations SURVIVE into the sibling
   alternative's world.
2. The sibling's clash then has a dependency closure carrying **both
   alternatives' track points of the same Or** (measured: the ⊥-implication
   held trigger CONNECTIONs to tp#54 AND tp#55). u29's all-siblings-refuted
   propagation reads that as a fully refuted decision whose stores hold only
   root-level externals → `cancellation_root_task` → wrong UNSAT.
3. The pre-existing leftover guard only covered `try_backtrack_or_branch_ddb`;
   `clashed_backtracking` (marking + propagation + ROOT-CANCEL) ran BEFORE it,
   unguarded. **Fix = gate the whole analysis on
   `unrestored_advance_count == 0`** (u02 `run_completion_on`). Poisoned
   searches degrade to validated plain chronological; `KM_HT_COW=1 KM_HT_DDB=1`
   never trips the guard (epochs restore completely) and keeps full DDB power.

**How it was found — ddmin the ontology, not the trace.** Log forensics on the
0.8 s reproducer (per-walk DDB-DISCARD-LIVE dump + per-walk dep chains, both
landed) proved chains complete (all NONE-prevs at IndependentBase) but could
not finger a rule. Delta-debugging ore_ont_12653 (script
`/tmp/ddmin_12653.py` on ws, ~10 min) shrank 264 lines → **5 axioms**
(AlternativePath⊑Path; MainPath≡¬AlternativePath⊓Path; Path⊑≥2 hasPathElement
.PathElement; Disjoint(Path,PathElement); PathOfLength2≡=2 …) where the wrong
root-cancel fires on **backtrack 1** with a 327-line trace — the tp#54+tp#55
double-dependency was directly visible. Landed as oracle test
`unrestored_advance_leftover_no_root_cancel` (fails pre-fix under KM_HT_DDB=1,
green in all 6 mode combos post-fix).

Also learned along the way:
- The A/B on the minimal ont EXONERATED the recog encoding (wrong verdict
  tracked DDB alone, RECOG irrelevant) — the "recog drops the ≤2 trigger half"
  hypothesis is FALSE.
- SIBLING dumps: the tag-0 EMPTY sibling in a 2-alt Or's dump is the decision's
  pre-marked CLASH track point (`nd.branch_track_points = nd.clash_track_point`
  chains it in as head) — not a phantom third alternative.
- My u02 advance label dump prints BEFORE the snapshot restore (pre-restore
  state) — don't read it as post-restore.
- Konclude's tracking-line dedup set is per-clashedBacktracking (cpp 6814
  stack local); our port matches (fresh `TrackedClashedDependencyLine::new()`
  per analysis, u29:895).

Validation: suite 1401/1401 (incl. new oracle); minimal repro pairwise=false
in plain/DDB/COW/COW+DDB/±REFUTED_DISCARD; big-ont AlternativePath,
PathOfLength2 0.8 s wrong-UNSAT → budget-STOP (correct-undecided).

Residual for the bridge production path: DDB-on-plain now degrades to
chronological the moment a probe's alternative creates nodes (common), so the
throughput answer for the disjunction family is **COW+DDB** (task #13's
databox-reuse piece) + per-subject defer (#14); the 100x slowdown on
genuinely-UNSAT probes (task #12's "missing" half) is now a pure throughput
question, no longer soundness.

## cont-17 (2026-07-08): complete-or-defer RESTORED via poison; 12653 bridge closure traded back

- **Commit 7a01372** (pushed): the 9635 completeness hole (bridge answered
  INCOMPLETE — contract violation) root-caused via ddmin to 4 axioms
  (`bridge_domain_survives_datatype_singletons`): an UNRESTORED alternative
  advance phantomizes deterministic ∃-successors created pre-branch; their
  consumed ∀⁻ never re-fires; an unrelated TOP-EM restore wipes `D(root)`;
  clash-free fixpoint ≠ model. Fix trio in-tree:
  1. u02: every unrestored advance sets `completeness_poisoned`; poisoned
     SAT/read-off verdicts DEFER (UNSAT stays sound — losing derivations only
     loses clashes); poisoning is deterministic ⇒ ONE poisoned subject
     early-bails the whole classification (no retry rounds).
  2. u02 `requeue_all_node_labels`: per-PASS requeue of label-IDEMPOTENT ops
     only (CCALL pos, CCSOME neg, CCIMPL, CCSUB, CCAND pos, CCOR neg).
     Successor-GENERATING ops excluded — requeuing them per-ADVANCE re-created
     successors every pass and OOM-wedged ws (lesson: per-pass, idempotent-only).
  3. bridge: KM_BRIDGE_COW_CONFIRM opt-in escalation (correct but uniformly
     slow — off until per-node COW localization).
- **Universe filter lesson survives** (067aaa4): `tin.concepts` carries
  frontend-synthetic markers (`Q_n`/`aux_`/`def_`/`__`); refuting one marker
  candidate = full SAT search. Filter candidates+subjects via
  `cb_to_ht::is_internal/is_bottom`. This was what made 12653 classify in 2.4s.
- **Cost of the poison semantics**: 12653/541/9635 bridge arms now DEFER
  (their probes take unrestored advances). Early-bail makes the defers cheap:
  12653 10.0s, 541 20.1s, 9635 211.6s (bridgeval-48395662). The 067aaa4-era
  12653 km-level closure (20.2s sig-identical) is TRADED BACK until per-node
  COW localization (Konclude task-fork shape) or COW+DDB throughput lands.
- **KM_HT_BRIDGE=1 panel 48395663** (584 onts, same-era Konclude): km 575 ok /
  9 timeout, gold 1157 MATCH + 2 DIFF = contested 2669/15516 (km right),
  faster+lighter 358/575 (62%), median wall 0.23s vs Konclude 0.29s, median
  mem 32MB vs 136MB. Timeout set: 541 3215 7581 7914 9663 9724 10621 12653
  14817 (9635+7499 SOLVE at baseline now; 7581/9724/10621 flipped IN —
  bridge-off control panel 48398378 pending to attribute).

## cont-18 (2026-07-09): unsat-cache learning live (KM_HT_UNSATCACHE) + Arc-COW hash satellites

- **cowddb-48445184 family matrix COMPLETE + uniform**: 12653/541/9635/3215
  ALL >600s under cow_ddb AND cow_ddb_rest where plain defers in
  10.0/20.0/216.6s (+3215 tail). Search volume is the single residual —
  Konclude's reducer for it is the unsatisfiable cache = learned nogoods.
- **1fc2618 wires the (fully ported, dormant) unsat cache live**:
  - Write side already existed: u29 clashedBacktracking →
    writeClashDescriptorsToCache (cpp 6844/7009/7056/7332) → u22 guards
    (single node level, terminology concepts, no nominals, no atomic clash)
    → occurrence cache. It no-opped because NO HANDLER was installed.
  - Bridge env now installs the handler (`install_bridge_unsat_cache`);
    `reset_probe_env` CARRIES it across probes → cross-probe nogood reuse
    (Konclude shares the cache across all tests of an ontology).
  - Read probes at Konclude's rule points (generative strategy =
    constant-true): OR disjunct add (u03 push + u02 advance, cpp 16908),
    SOME/ATLEAST successor gen (u08, cpp 14351/16132, abort on hit),
    at-most init (cpp 14959), merged node (u15 tail, cpp 15457). All
    pending-gated (raise_clash OVERWRITES the signal).
  - **KM-specific soundness gate (u21)**: reads disabled whenever
    unrestored_advance_count != 0 — a nogood firing on a
    phantom-contaminated label MANUFACTURES a clash = wrong-UNSAT class
    (same as 7c521cb). Mirrors the u29 write gate. Production combo =
    KM_HT_COW+KM_HT_DDB+KM_HT_UNSATCACHE (gate never trips under COW).
  - **Bug found**: bridged concepts carry no ConceptProcessData → tag
    stamping no-opped → cache silently INERT. Fix: lazy alloc at the stamp
    site (cache/unsat.rs; Konclude's preprocess guarantees the data exists).
  - In-process write→read round trip verified: process_customs_events
    updates reader hashes directly (no slot-swap latency).
- **Arc-COW extended** (also 1fc2618) to role_succ_hashes / distinct_hashes /
  succ_role_hashes (0c5848f shape; 4 role_succ split-borrow sites get
  per-site Arc::make_mut; disjoint_succ_role_hashes stays plain — rare).
- Validated: suite 1409/1409 × {default, UNSATCACHE+DDB, UNSATCACHE+COW+DDB,
  ATMOST_REST+COW+DDB} on ws; new test unsat_cache_warm_probes_keep_verdicts
  (cold UNSAT → warm UNSAT → warm SAT control + handler survives reset).
- **PENDING: unsatcache-48454415** (IBEX km-dev): cow_ddb vs cow_ddb_uc vs
  plain on 12653/541/9635/3215 — decides whether nogood learning un-defers
  the family. Output /ibex/scratch/hohndor/km-dev/unsatcache-<jobid>.out.

## cont-19 (2026-07-09): UNSAT-CACHE VERDICT = NET-NEGATIVE; investigation closed

Full attribution chain (parallel wave: ws suite + ws probes + IBEX 12-leg
parallel matrix 48471746, all legs concurrent -> full matrix in ~15 min):
1. First A/B (48454415, cancelled): uc legs = control timeouts. Counters
   (9c03476) showed 0 written / 0 hits -> WRITE-side failure.
2. Root cause 1: bridged concepts carry NO TERMINOLOGY -> u22's
   `is_valid_unsat_cache_tracked_concept_descriptor` rejects every line
   (guard intent: exclude non-ontology-stable query concepts). Fix =
   terminology-stamp sweep in bridge_tinput (2nd missing-preprocess-invariant
   bug after ConceptProcessData). Only other get_terminology consumers are
   behind the computed-consequences handler (never installed in bridge) —
   stamp is safe.
3. Post-fix A/B (48471746): cow_ddb_uc STILL = control timeouts on ALL FOUR
   (12653/541/9635/3215); plain unchanged (10/20/222/17s).
4. DECISIVE ws attribution on 12653 @ budget 1s: control (COW+DDB) finishes
   17s; +KM_HT_UNSATCACHE cannot finish in 400s. Once writes actually flow,
   the cache is a >20x RUNAWAY TAX with no pruning. Suspects (unprofiled,
   moot while flag off): per-closure get_sorted_clashed_descriptors O(n^2),
   unbounded ontology-arena growth (lazy ConceptProcessData + tags per
   write), cache-entry flooding without cross-probe reuse, write path
   running outside the probe-deadline check.
5. STRUCTURAL point: Konclude's u22 gate only caches SAME-node-level chains;
   this family's conflicts are root-disjunction + ∀-propagation across
   levels -> largely uncacheable by THIS mechanism even in Konclude.
DECISION: KM_HT_UNSATCACHE stays opt-in (off). Keep the correctness pieces
(terminology stamp, lazy ConceptProcessData, counters) — they make the
subsystem sound + measurable. Next lever for the family (Konclude-faithful):
saturation-first probe answering — Konclude decides ~95% by saturation
before any tableau search (12 saturation units are ported, not wired into
bridged_unsat); the family's pair probes are exactly what saturation
short-circuits. Ops lessons: timeout+setsid orphans the child (kill by PID);
name-based PID sweeps kill concurrent legs (sweep only recorded PIDs);
cargo test binary hashes are metadata-stable (same name after rebuild —
check mtime, not hash).

### cont-19 CORRECTION: the "runaway tax" was a SLOT-RING DEADLOCK; A/B still open
- The >20x slowdown was NOT a cache tax: gdb on the hung 5-class warm-probes
  test showed 100% CPU inside `process_customs_events` →
  `wait_cache_write_prepared` — the write-slot ring had ONE slot
  (`OccurrenceUnsatisfiableCache::new(1,..)` in the install helpers), and
  with one slot the activation pins it through the reader's next-pointer
  while the release needs a SECOND slot to displace it → the C++
  msleep-and-rescan wait (a CONCURRENT-reader protocol) spins forever
  in-process. Konclude production sizes the ring `workControllerCount + 2`
  (CExperimentalReasonerManager cpp 58).
- Fix: ring = 3 everywhere (bridge install + test helpers) +
  `wait_cache_write_prepared` bounded rescan (a full pass that frees nothing
  returns no-slot; caller SKIPS the write — lost nogood line, never a hang).
- CONSEQUENCE: the 48471746 "null A/B" and the 17s-vs->400s attribution are
  BOTH invalid (uc legs were spinning, not searching). The REAL
  cow_ddb vs cow_ddb_uc A/B (+ counters) is still pending post-fix.
- The same-level-only structural point (u22 caches single-level chains,
  family conflicts are cross-level) STANDS as a prior — but is now a
  hypothesis for the counters to confirm (expect writes small / hits ~0 on
  the family if true), not a concluded verdict.

### cont-19 FINAL (1c931e7): unsat-cache functional; verdict = ZERO REUSE on the family
- Post-fix measurement (ws, COW+DDB+UNSATCACHE, budget 1s): cache overhead
  ~ZERO (12653: 17.2s with vs 17.0s without); counters: 12653 = 27,984
  lines written / 0 hits, 541 = 87,449 / 0 hits. The family's nogood lines
  carry seed + branch-specific atoms and NEVER recur as a label subset —
  unsat-cache learning cannot prune this family (valid negative result;
  the earlier "tax"/"null" readings were the slot deadlock). IBEX matrix
  resubmission SKIPPED: the two hardest members answer the question; a
  full-family rerun would measure nothing new.
- Konclude's speed on the family is therefore saturation + absorption, not
  its unsat cache. NEXT LEVER (confirmed twice over): saturation-first
  probe answering — wire the 12 ported saturation units in front of
  bridged_unsat (Konclude decides ~95% by saturation, tableau on residue;
  docs/KONCLUDE-STUDY.md).
- KM_HT_UNSATCACHE: correct, cheap, measurable, OFF by default. Possible
  future value on repeated-similar-label workloads (big-taxonomy
  classification); test via one panel if ever relevant.
