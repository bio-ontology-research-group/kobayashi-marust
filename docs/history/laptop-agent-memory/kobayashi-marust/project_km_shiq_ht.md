---
name: project_km_shiq_ht
description: 2026-06-22 SHIQ hypertableau plan to solve the disjunction family; key finding that inverse-edge propagation already works
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

Plan `sorted-wishing-cloud.md` (approved 2026-06-22): solve the disjunction
family by extending KM's `Ht` (engine/src/hypertableau.rs) from ALC(H) to SHIQ
(inverse + qualified number restrictions + pairwise blocking) + Konclude-style
triggered absorption + a lazy per-concept saturation gate. **Nominals deferred**
(user decision): family is half SHIQ (1603,12653,16444,7581 + 5303-already-solved),
half SHOIQ (10702 207 nominals, 9540 13, 10908 4, 15672 2, 6934 1). Saturation gate
INCLUDED (user decision) — Konclude's ~95%-skip CLEAN/CLASHED/INSUFFICIENT gate,
reuse elc + cert.

**KEY FINDING (de-risks Phase 2):** the agent claim "inverse is inert in Ht" is
WRONG about the mechanism. cb_to_ht (orchestrate/cb_to_ht.rs:506-517) emits inverse
bridging clauses `r(x,y)->r⁻(y,x)` + reverse; these FIRE via role_triggers ->
fire_anchor_edge (hypertableau.rs:1026) -> apply_head HeadItem::Edge (973) ->
add_edge. So inverse EDGES are created already. The real blockers for inverse onts:
(1) routing guard ht_routable (race.rs:425) rejects tin.inverse; (2) subset
blocking (block_mode default 1) is UNSOUND under inverse -> need pairwise
(block_mode==3, already implemented at compute_blocked 2892-2939, the exact HermiT
4-tuple). So Phase 2 ≈ "lift guard for nominal-free inverse onts + force pairwise".

`KM_HT_FORCE=1` (race.rs:471) bypasses the guard. To isolate HT from CB (CB is the
memory hog on these onts): set `KM_ENGINE_BIN=/bin/false KM_HT_MODE=fallback
KM_HT_BUDGET_S=0` -> CB errors instantly, fallback uses HT alone (race.rs:645-649).

**EMPIRICAL RESULTS (2026-06-22, IBEX cn604, HT-only forced):**
- Phase 2 inverse mechanism is SOUND: two cargo unit tests added+PASS
  (inverse_role_propagates_universal_back / inverse_role_consistent_without_clash in
  hypertableau.rs tests). Inverse-edge bridging fires, ∀r⁻ propagates back, no
  over-propagation. So Phase 2 ≈ DONE at mechanism level (just needs guard-lift +
  pairwise auto-select wiring).
- **16444 (inverse-only) times out HT-isolated** at 240s even WITH pairwise (block 3)
  AND all existing convergence levers (TRIGABS+CONTRA+HARVEST): 12.6GB plain ->
  9.9GB with levers, still no termination. **CONCLUSION: SHIQ tableau expressivity is
  necessary but NOT sufficient. The family needs the SATURATION GATE (Phase 5) — it's
  a large ont dominated by per-concept SAT-test COUNT, exactly Konclude's
  CLEAN/INSUFFICIENT gate target.** Per-ont recovery cannot be validated incrementally
  (levers interdependent): validate each phase's SOUNDNESS via fast ws cargo unit tests,
  then ONE combined IBEX family sweep once Phases 1+3+5 stack.
- STRATEGIC FORK noted (not yet decided): the saturation gate could feed the
  already-sound CB engine (handles full SROIQ incl. nominals) instead of / in addition
  to HT — would cover the 5 nominal onts too and avoid needing a SHOIQ tableau. Plan
  currently targets gate->HT per user "implement in HT".

**16444 IS A HARD OUTLIER (2026-06-22, ws):** 230,005 clauses, 21 inverse + 110
disjunctive clauses. ofn fast (1.6s). Defeats ALL planned levers: SHIQ tableau
per-concept tests timeout; +TRIGABS+CONTRA+HARVEST timeout; **QoSat saturate_global
does NOT terminate (>200s, never reaches tally)** on its inverse model. Root cause:
HT does N per-concept full model-builds over 230k clauses (~thousands of named
concepts) = hopeless; the fix is HermiT/Konclude's "build ONE model, read off the
quasi-order, residual-test only" architecture — which is exactly what QoSat attempts
but it (a) doesn't terminate on inverse and (b) was unsound on the disjunction family
(qo_deadend -2). So 16444 needs MAJOR work (a terminating QO classification with
inverse) — DEFER as outlier. PIVOT: the SMALLER cardinality onts (1603=2937 cls,
12653, 7581 near-Horn) were CB-specific blowups; their HT tractability is untested
and likely better — build Phase 3 (cardinality merge rule) and test THEM first. Don't
over-index on 16444.

**Phase 1 already built+wired+gated-off**: trigger_absorb (hypertableau.rs:1432,
KM_HT_TRIGABS) + contrapositives (1369, KM_HT_CONTRA), called in Ht::new (2548-2562)
BEFORE recs/global_disj/concept_triggers build (2563+) so absorbed clauses correctly
drop out of global_disj. Prior "TRIGABS inert on 5303" verdict is misleading: 5303 is
the ONLY family ont reaching Ht today (others guard-blocked), and 5303 has POSITIVE
exclusive disjuncts (no negative disjunct for trigger_absorb to key on). Absorption
only becomes measurable AFTER SHIQ onts reach Ht.

**Phase 3 (cardinality) = the genuinely new work** — IN PROGRESS (2026-06-22):
- DONE+TESTED (gated KM_HT_NUMBER, 117 lib tests green, production untouched):
  in_edges now carries DepSet; new Ext fields `number`/`merged: Vec<Option<Node>>`;
  `resolve()` (follow merge chain) + `merge_into(a,b,mdep)` (copies victim's concepts
  + in/out edges onto lower-id survivor under union dep, trail-recorded Trail::Merge,
  backtrack-safe); apply_head single-Eq head -> merge_into (multi-Eq still bails
  unsupported). Tests: functional_merge_forces_clash / _consistent_when_compatible
  (+ the 2 inverse tests). Handles ≤1/functional (the common case).
- REMAINING for full ≤n completeness: (1) resolve()-threaded SUCCESSOR COUNTING so a
  parent's edges to victim+survivor count as ONE successor for ≤n (else over-counts ->
  incompleteness in the merge-enables-SAT direction); (2) exclude merged victims from
  obligation expansion + blocking (else phantom subtrees; currently sound-but-wasteful
  for unsat detection); (3) multi-Eq (≤n n≥2) merge-DISJUNCTION branch (extend
  eval_disj/pending with merge disjuncts). (4) ≥n n-successor generation
  (process_obligations creates only 1 succ).
- cb_to_ht FENCES inverse+number (cb_to_ht.rs:559-564, record-only, clauses NOT
  dropped) + emits Eq heads (439-495); remove fence + lift ht_routable guard once
  merge complete.

**END-TO-END TEST RESULTS (2026-06-22, the hard wall):**
- 7581 (only 1 functional role -> FULLY covered by single-Eq merge; near-Horn; inv=2,
  trans=3): forced-HT + KM_HT_NUMBER + pairwise = TIMEOUT, only 1.5GB (slow, not mem).
  Stats: 0 classify-p1 lines -> the GLOBAL model build (consistent(&[])) does NOT
  terminate, even after adding victim-exclusion from obligations+blocking. The
  merge+transitivity+inverse+blocking interaction doesn't fold to a finite model.
  CONTEXT: HermiT ALSO TIMES OUT on 7581 (Konclude-only) -> genuinely hard.
- PATTERN across the family: the wall is CONVERGENCE/TERMINATION, not expressivity.
  16444 = per-concept test COUNT (needs QO build-one-model). 7581 = model-build
  non-termination under merge+trans+inverse. QoSat gate = doesn't terminate on inverse.
  Fully solving the family = MAJOR multi-week research (correct terminating SHIQ
  tableau + QO architecture), uncertain payoff (some onts defeat even HermiT).
- BANKED (validated, gated KM_HT_NUMBER/KM_HT_FORCE, 0 production impact, 117 lib
  tests green, UNCOMMITTED): inverse roles sound+tested; functional-merge primitive +
  in_edges-dep + resolve + victim-exclusion. Real foundations; recoveries need the
  hard core. USER CHOSE: press on with the QO build-one-model architecture.

**QO PREREQUISITE = terminating SHIQ build. PRECISE BLOCKER (2026-06-22):** 7581
global build (KM_HT_GLOBAL=1, number+pairwise+blockskip) hangs with: nodes ≤200 (no
[blocking] line which prints at nn>200) AND no heartbeat even at KM_HT_HB=30000 (tick
< 30k in 40s). => stuck in a SINGLE non-looping-back call (the clause-firing fixpoint),
NOT dfs/expansion. TRANSITIVITY RULED OUT: regenerated tin with KM_HT_NO_TRANS_ENC=1 = BYTE-IDENTICAL
(51665644) and still hangs -> 7581's transitive roles add no propagation clauses, not
the culprit. So the loop is merge_into × INVERSE bridging (merge copies edges ->
fires r<->r⁻ bridging + functional clause -> ??? non-terminating clause-firing fixpoint
on bounded nodes). SMALL REPRODUCER TERMINATES: merge_inverse_existential_terminates test (functional
merge + inverse + ∃-over-inverse, 3 nodes, 1 merge) PASSES — merge primitive is sound
+ terminating on small cases. GOTCHA: all earlier "reproducer hang" signals were
`cargo test --release` RECOMPILE timeouts, not execution; compile harness with
`--no-run` first, THEN run under timeout.

7581 HANG NARROWED by instrumentation (all 4 obvious modes RULED OUT): NOT node growth
(nodes ≤200, no [blocking] line), NOT merge explosion (<100k merges), NOT propagate
event-churn (<2000 heartbeat events in 90s @ KM_HT_HB=2000), NOT explosive
rec_match_flex join (added gated RMF_STEP_CAP=8M step cap -> bails unsupported + logs
HUGEMATCH; NEVER FIRED on 7581). So it's a slow/looping inner region elsewhere with
bounded nodes. Small reproducer won't reproduce it. LOCALIZING NEEDS: perf/flamegraph
on the IBEX binary running 7581 global build, OR ddmin clause-reduction. ~30 remote
round-trips spent.

ADDED (gated KM_HT_NUMBER, 118 lib tests green, 0 production impact): RMF_STEP_CAP
match-enumeration cap (sound bail on join overflow) + Ext.merges counter. All Phase 2/3
work UNCOMMITTED, ready to commit as the durable base for the QO effort.

**KONCLUDE TRACE OF 7581 (2026-06-22, PIVOTAL) — Konclude v0.7.0 prebuilt binary at
/ibex/scratch/hohndor/km/bench/reasoners/Konclude-v0.7.0-*/Binaries/Konclude (needs
libpcre.so.3 -> symlink /usr/lib64/libpcre.so.1; run with -w1 -a -v).** Konclude
classifies 7581 in 5.6s total. Log: expressiveness **'SRIF'** (Inverse+Functional+
chains+trans, NO qualified-number-Q, NO nominals — so 7581 "card=1" = 1
FunctionalObjectProperty, my single-Eq merge already covers it; ≤n n≥2 NOT needed).
KEY: "Ontology has been **SUFFICIENTLY SATURATED, extracting data for classification**"
+ classification 525ms => Konclude does ~ZERO per-concept tableau tests; the
non-branching saturation is SUFFICIENT. CONFIRMS the SATURATION GATE (Phase 5) is THE
lever, NOT the SHIQ merge tableau. KM hangs because it does N per-concept tableau tests
AND its tableau build loops on SRIF. RIGHT ARCH = Konclude's: terminating non-branching
saturation, sufficient for SRIF/near-Horn, residual tableau only for genuinely
disjunctive concepts. KM HAS this (QoSat) but it DOESN'T TERMINATE ON INVERSE -> THE
precise tractable fix. NEXT: trace KM_HT_QO QoSat::saturate_global on 7581, find why
the shared-node park-saturation diverges with inverse bridging, fix it. Konclude src
/tmp/Konclude; HermiT TIMES OUT on 7581 so can't trace a success there.

**CRITICAL DISCOVERY (2026-06-22) — invalidates ALL prior IBEX conclusions on
inverse/number onts:** tableau.rs run_json (~line 4493) has a SECOND routing gate
independent of race.rs ht_routable / KM_HT_FORCE:
`if KM_HT && !inp.number && !inp.inverse && inp.nominals.is_empty() { Ht/QoSat path }`.
So EVERY IBEX run on 7581/16444 (inverse onts) via tableau_cli FELL THROUGH to the
LEGACY tableau (tableau.rs, known to hang/error on real ORE onts) — my Ht + merge +
QoSat code NEVER RAN on them. The 7581/16444 "HT hangs" were the LEGACY tableau, NOT my
code. Only the cargo unit tests (call Ht directly) ever exercised my code. FIX: relaxed
the run_json gate to `ht_force || (...)` so KM_HT_FORCE=1 routes inverse/number onts
into Ht/QoSat. NOW re-running 7581 QoSat trace with KM_HT_FORCE=1 — first time my code
actually runs on a real inverse ont. Re-evaluate everything from here.

**COMPLETE DIAGNOSIS (2026-06-22, via Konclude trace + QoSat instrumentation):**
7581 = 72,989 named concepts / 455k clauses, SRIF. Konclude solves in 5.6s via
saturation-sufficiency (~0 tableau). KM's QoSat IS the right architecture but had TWO
real bugs, BOTH FIXED:
  1. run_json gate (tableau.rs:4493) sent inverse/number onts to LEGACY tableau (hangs)
     — FIXED: now honors KM_HT_FORCE (`ht_force || (...)`).
  2. QO_NODE_CAP=8000 (tuned for 5303-family) bailed instantly on 73k concepts ->
     fallback hang — FIXED: cap = named.len()+500k (scales with ontology).
With both fixed, QoSat on 7581: nodes BOUNDED at ~73k (does NOT diverge!), but SLOW —
after 2M drain steps edge_work=860k pending; times out at 180s. Bottleneck = naive
worklist saturation + O(nodes) match_body scan (the (None,Some) unbound-source role
case, hypertableau.rs ~2543 scans all nodes). NOT a soundness/termination problem — a
SCALE/EFFICIENCY problem. THE FIX: make QoSat saturation edge-indexed (port the ELK
backward-link propagation I already added to elc, see [[project_km_elc_elxx]]), OR
extend elc to inverse/functional (SRIF) and route SRIF onts there. This is the genuine
remaining lever for the family (Konclude-style efficient sufficient saturation).
All gated KM_HT_FORCE/KM_HT_NUMBER, 118 lib tests green, UNCOMMITTED.

**COMMITTED (2026-06-22, branch payg-strategy):**
- `eaf6662` — SHIQ inverse + functional-merge foundations + the two routing-gate
  fixes (run_json KM_HT_FORCE bypass; QoSat node-cap scaling). 118 tests.
- `9ee2e7f` — **QoSat edge-indexed saturation (the elc BLP port).** Added
  `QoSat::in_edges` (incoming-edge index → match_body (None,Some) predecessor case
  is O(in-degree) not O(#nodes)) + `QoSat::role_clause_trig` (role-keyed firing →
  an r-edge fires only clauses mentioning r, no full role_clauses clone per edge).
  Result-IDENTICAL by construction. New test `qosat_edge_index_role_chain`. 119 tests.
- `36912ee` — dropped per-node `self.global.clone()` (O(#nodes×|global|) alloc) +
  split drain counters QODRAIN/QONODE/QOEDGE (gated KM_HT_TRACE). 119 tests.

**7581 QoSat MEASUREMENT (IBEX, KM_HT_FORCE+KM_HT_QO, CB isolated, FULL 420s) —
RE-TARGETS THE DIAGNOSIS:** even WITH the edge indexes, QoSat saturation does NOT
converge in 420s (~1GB, CPU-bound, EXIT=124). The split counters are decisive:
**one QODRAIN tick (2M lit-pops), ZERO QONODE pops, ZERO QOEDGE pops.** The whole
420s is spent in the LITERAL (concept-clause) propagation loop; it NEVER REACHES
the role/edge phase the indexes optimise. So the prior "edge-index is the lever"
diagnosis was WRONG about 7581's wall — the wall is upstream: the
O(#seeded-nodes × concept-clause fires) volume of saturating ONE shared node for
EACH of 72989 concepts against 455583 clauses (a popular superclass lit fires
thousands of clauses × 73k nodes = billions of fire_concept_clause calls). The
edge index is correct + necessary + a clean win on onts that DO reach the edge
phase, but it is NOT 7581's lever. **GENUINE NEXT LEVER = ARCHITECTURAL, not more
saturation indexing: don't seed+saturate 73k independent nodes.** Either (a) extend
elc to SRIF (inverse+functional) and route SRIF onts to its told-subsumer single
pass [[project_km_elc_elxx]], or (b) make the gate per-concept (saturate only the
concept under test, not all 73k at once). Stop micro-optimising the all-nodes
saturation — it can't crack 7581. ~6 IBEX round-trips spent confirming this.

**7581 SHOWDOWN (2026-06-22, IBEX job 47724160, CB isolated, gold compare) — BOTH
options the edge-index entry named were built+measured head-to-head. NEITHER WINS:**
- **Per-concept QoSat gate (KM_HT_QO_PC, commit 57af372, SOUND, KEPT gated):** one
  fresh single-seed `saturate` per query concept (QoSat::reset reuses indexes;
  complete_roles re-fires role clauses for guard-after-edge; node_cap raised). 5
  unit tests. RESULT = **TIMEOUT 280s** (1.78GB); diag shows <5000 concepts done in
  200s (<25/s) — no told-subsumer sharing ⇒ re-walks shared closures (~O(N²) on
  deep hierarchies). Sound but too slow. Kept gated.
- **elc inverse edges (KM_ELC_SRIF, commit e8ba729, UNSOUND, REVERTED 80001cc):**
  materialise reversed edge (d,S,c) from R(x,y)->S(y,x). RESULT = **66s but WRONG**:
  EL saturation derives ⊤⊑⊥ (declares 7581 inconsistent; gold consistent w/ 565k
  subs). ROOT CAUSE: EL rules (R⊥-edge, NF4, NF7) ASSUME edge (c,R,d) came from an
  existential c⊑∃R.d; a materialised inverse edge breaks that invariant so a ⊥
  filler propagates ⊥ backward unsoundly. Naive edge-reversal is NOT a sound ELI
  encoding in the shared-context model. Reverted. Sound ELI needs a SEPARATE
  backward-concept propagation channel (Kazakov consequence-based Horn-SHIQ) — big.
- **VERDICT: 7581's real lever = a sound SHARED (told-subsumer) ELI saturation —
  elc's efficiency WITH the CB engine's soundness. Not a quick variant of either.**
  Both flags off by default ⇒ zero corpus regression. The CB engine already does
  sound SROIQ but doesn't scale on 7581; that scaling (or a proper ELI elc) is the
  remaining work. HermiT also times out on 7581; only Konclude solves it.

Build: ws (`cargo build --release`, 3m22s clean, glibc != IBEX) + IBEX
(/ibex/scratch/hohndor/km/engine, runs next to corpus+gold+harness). Corpus+gold on
dragon /ibex/scratch/hohndor/km/{corpus,gold,harness}. See [[project_km_hybrid_cb_ht]]
[[project_km_5303_perstep_cost]] [[project_km_qo_deadend]].
