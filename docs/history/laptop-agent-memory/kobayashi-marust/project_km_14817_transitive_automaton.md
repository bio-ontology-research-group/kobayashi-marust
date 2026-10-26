---
name: project_km_14817_transitive_automaton
description: 2026-06-28 14817's residual 71 = REAL transitive-part_of subsumptions KM misses; Konclude role-automaton mechanism traced; fix = port automaton ∀-propagation
metadata:
  type: project
---

# 14817 residual (71 incomplete) = transitive-part_of composition gap, NOT disjunction/contested-gold

**DEFINITIVE (2026-06-28):** Konclude asserts `UBERON_0002288 ⊑ UBERON_0002200` as a
DIRECT subsumption (2288's direct supers in Konclude's classified output =
{UBERON_0001886, UBERON_0002200}) — a REAL derivation, not an ore_canon closure artifact.
2200 ≡ ∃part_of.UBERON_0000033(head) ⊓ UBERON_0002049; KM derives the 0002049 conjunct,
not ∃part_of.head. KM agrees with Konclude on 12/13 supers of 2288 (only 2200 missing) and
gets 12/17 subclasses of 2200 (short part_of chains) — so it's a real KM incompleteness on
the DEEP transitive-part_of chains, disproving the canon-artifact hypothesis. Both KM
engines (QoSat saturate + Ht consistent) miss it.

**Konclude mechanism (traced with instrumented Konclude on ws:~/konclude-build, KTRACE=1):**
transitive roles + RIAs + sub-roles are compiled into ONE per-role AUTOMATON, reified as
concepts (CRoleChainAutomataTransformationPreProcess.cpp). The part_of automaton trace
([AUTOMAT-build]) shows: main transition beginState--part_of-->endState (carries the
restriction); SUB-ROLE/chain transitions (e.g. has_start∘start_of) GLUED into begin/end
states; and a TRANSITIVE ε self-loop endState--ε-->beginState that makes ∀part_of.C chase
ALL part_of-successors transitively. The ∀-rule (applyAutomatTransactions / applyALLRule in
CCalculationTableauCompletionTaskHandleAlgorithm.cpp) propagates the next-state concept to
every R-successor and RE-FIRES when new edges are created (addConceptToReapplyQueue keyed by
role). Subsumption A⊑D (D=∃R.C) decided by refutation: ¬D=∀R.¬C, the automaton propagates
¬C transitively, clash at the forced existential.

**KM's gap:** KM keeps the three encodings SEPARATE and they don't compose in the
saturation: transitivity = `__trans` P-concepts (clause2 `R(x,y)∧P(y)→P(x)`, backward);
sub-roles = bridge clauses `BSPO(x,y)→part_of(x,y)` (all 19 emitted); chains = `__chain`
concepts. All emitted (dropped=0, fenced=0; 6589 __trans + 1800 __chain). But in 2288's
per-concept model (173 nodes) head(0000033) is NEVER forced — the composition of
transitive part_of WITH the sub-role/chain edges that reach head doesn't fire. The
documented gap (preprocess.rs chain_clauses note: "11745 needs chain to compose with
TRANSITIVE part_of").

**FIX = port Konclude's role automaton** (transitivity ε-loop + sub-role/chain transitions
folded into one automaton, ∀-forward-propagation re-fired on new edges). Major feature:
frontend automaton build + saturation/tableau ∀-propagation. This IS the r-Succ fix done
the Konclude way. Supersedes the separate __trans/__chain encodings.

**Instrumented Konclude on ws:** ~/konclude-build/Release/Konclude (KTRACE=1 gates
[AUTOMAT-build] for BFO_0000050, [AQALL-newedge]/[ALL-newedge] ∀-propagation, [EDGE-create],
[CLASH]). Run: `./Release/Konclude classification -w 8 -i /tmp/14817.owl -o OUT`. Full run
~52s; KTRACE flood throttles via pipe so use a small module (/tmp/mod2288.owl) for readable
traces. KM diagnostics committed: KM_HT_QO_TESTONE=A,B (adjudicate pair via complete Ht),
QOPROBE2 (model dump). KM is SOUND + 99.994% complete on 14817 (~12s) with KM_HT_QO_INPLACE.

Related: [[project_km_rsucc_gap]] (transitive+inverse, same family 12698/7914),
[[project_km_card_recognition_nonconverge]].

## RUNTIME TRACE (2026-06-28, instrumented Konclude ws:~/konclude-build, KTRACE=1)
Confirmed the forward propagation directly. `[AQALL-newedge] node N --part_of--> node N+1 : propagate <stateTag> := ( (All RO_0002202. t) AND (All RO_0002207. t) AND (All BFO_0000050. <SAME stateTag>) AND (All has_start. t) )`. ONE automaton-state concept propagates forward across each part_of edge, contains `All part_of.<itself>` (ε self-loop = transitivity) so it re-propagates down the whole chain (traced node 2→3→4→5→6…), AND carries the sub-role/chain transitions (All has_start.) in the SAME state. So one forward propagation walks part_of + sub-roles + chains uniformly; the restriction rides to every part_of-reachable node; clash there proves the subsumption. getConceptString renders nested fillers as TAGS not IRIs (so IRI-substring trace filters give false zeros — filter on tags or instrument the classifier). Konclude classify on 14817: preprocess 1.5s, precompute 3.9s, classify 20.5s (-w 8). KSATDBG: satTests=58365 calculatedSubTests=660 possSubsumers=7851. Instrumentation points: CRoleChainAutomataTransformationPreProcess.cpp:426/511/1401/1494 ([AUTOMAT-build]); CCalculationTableauCompletionTaskHandleAlgorithm.cpp:9669/9713/16314/16356 ([AQALL/ALL]-newedge/allsucc), :22310 ([EDGE-create]), :26964 ([CLASH]); .bak/.bak2 backups kept.

## IMPLEMENTATION PLAN (port Konclude role automaton into KM)
1. Frontend: per complex role R (transitive ∪ has a RIA ∪ is a super of sub-roles), build an NFA from its chains; transitive R = (R)* self-loop. Reify states as conjunction concepts, transitions as `All role.next-state`. Rewrite each `∀R.C` (complex R) into the entry state seeding start. Replaces transitivity_clauses/chain_clauses/sub-role-bridge for complex roles.
2. Saturation (QoSat + Ht): on an R-edge x→y, propagate the state's next-state operands to y (forward ∀); re-fire when a new R-edge is later created (reapply keyed by role). Self-loop makes it transitive.
3. Validate each step against the instrumented Konclude oracle (state structure, propagation, node counts) + 14817 incomplete=71→0 + corpus soundness sweep (no regressions). Needs Lean re-cert (calculus change) per CLAUDE.md.

## MILESTONE (2026-06-28, commit 3aa77f9): KM_TRANS_CHAIN_COMPOSE built + validated
Gated (default OFF) frontend pass `transitive_chain_compose_clauses` in preprocess.rs (wired in augment_with_chains). For chain R∘S⊑U with U⊑*T (T transitive) + each P=__trans__T__{C}: emit `S(y,z)∧P(z)→__cmpp__S__P(y)`, `R(x,y)∧__cmpp(y)→P(x)`, `S(y,z)∧⋀C_i(z)→__cmpc__S__P(y)`, `R(x,y)∧__cmpc(y)→P(x)`. Sound (T trans+U⊑T ⇒ x T z). Split env-gate from logic (transitive_chain_compose_impl) for testability. VALIDATED: synthetic /tmp/cctest.ofn positive (A⊑D derived via has_start∘start_of⊑sub⊑partOf), /tmp/cctest_neg.ofn negative (broken chain ⇒ NO A⊑D = sound, no over-derivation), unit test trans_chain_compose_feeds_reachability, 175 tests pass. Tin regen: `KM_TRANS_CHAIN_COMPOSE=1 KM_DUMP_TIN=/tmp/14817_cc.tin KM_HT_FORCE=1 km classify /tmp/14817.owl` → 290910 clauses (was ~282k), 4158 __cmpp + 4158 __cmpc concepts incl `__cmpp__start_of____trans__BFO_0000050__UBERON_0002288`. Ids in cc.tin: UBERON_0002288=39286, UBERON_0002200=36901 (baseline recog.tin: 39245/36889).
BLOCKER for 14817 recovery: TESTONE consistent(2288⊓¬2200) on cc.tin STACK-OVERFLOWS on 'main' thread after building model (170s, only 178MB RSS — recursion depth not memory; RUST_MIN_STACK=4GB inert ⇒ main thread). Baseline TESTONE doesn't overflow (just slow, times out 180s). Need: main-thread stack fix (run reasoning on a Builder::stack_size thread) or iterative consistent() recursion. THEN corpus regression sweep + Lean re-cert before default-on. NEXT: test whether the REAL qo_classify_perconcept path (not the TESTONE probe) overflows too, or only the probe.

## TIMING FINDING (2026-06-28): composition is NOT the slowdown; KM-QO classify is inherently slow on 14817
ws CLEAN (after killing a 67-min 54-core km ORPHAN that had saturated the box — KM_DUMP_TIN classify child orphaned the no-orphans rule again; kill by PID 4081540). With load≈0:
- cc.tin (composition) QO classify [KM_HT_QO + RESIDUE_COMPLETE + CARD_RECOG]: TIMEOUT 300s, 184MB RSS (CPU-bound).
- recog.tin (baseline) QO classify: ALSO TIMEOUT 300s, 160MB RSS.
- Restricting tin queries to a SINGLE concept (2288) does NOT speed it up — baseline-one AND cc-one both timeout 120s ⇒ the QO classify does a GLOBAL saturation pass regardless of the queries list.
CONCLUSION: the 300s timeout is pre-existing KM-QO architecture (global/per-concept brute-force saturation), NOT caused by KM_TRANS_CHAIN_COMPOSE (baseline equally slow). Konclude does 14817 in 20s via LAZY pseudo-model filtering (KSATDBG calculatedSubTests=660 of 7851 possSubsumers — 95% confirmed cheaply). To recover 14817 in benchmark time needs the lazy classification / pseudo-model reuse (the in-flight task #4 / [[project_km_konclude_study]] P1/P2), independent of the (now-correct) transitive mechanism. Composition mechanism stays VALIDATED on synthetic + unit test; full-14817 completeness confirmation must wait for a tractable classify (longer budget sweep on unimatrix, or the lazy path). Added KM_TAB_STACK_MB large-stack worker thread in cli.rs run_tableau (fixes the main-thread overflow; uncommitted).

## CORRECTED LAZY-CLASSIFY DIAGNOSIS (2026-06-28, via docs/THROUGHPUT-GIANTS-HANDOFF.md + Konclude classifier trace)
14817's QO wall is NOT saturation speed. KM's QoSat global-forward PRECOMPUTE finishes in ~4s (≈Konclude's 3.0s precompute) — it seeds 58364 concepts and parks 763k disjunction INSTANCES = just 13 distinct global ⊤-disjunctions × 58k nodes. The wall: `quasi_order_classify` cannot CERTIFY those parked disjunctions in residue-complete, so it DEFERS to the branching `ht.classify` → 195-deep `Ht::dfs`→`compute_blocked` (the 5303 disjunction-search-convergence family). So the lazy-classify gap = the CLASSIFY phase, not the precompute. Konclude classifies per-concept against ONE precompute pseudo-model: deterministic-subsumer filter + isPseudoModelSubsumerPossible prune (concept-map: B has a DETERMINISTIC concept missing from A ⇒ prune A⊑B; role-map: cardinality + recursive successor-model compat) → only survivors get a real bounded tableau test (Konclude 14817: calculatedSubTests=660 of possSubsumers=7851). Konclude algo cited: COptimizedKPSetClassSubsumptionClassifierThread.cpp (main loop 755, isPseudoModelSubsumerPossible 1626-1708, calculateSubsumption 1298, prune update 2204); pseudo-model CClassificationClassPseudoModelData.h:54-93 (conceptMap deterministic-flag + roleMap lower/upperAtLeast/AtMost+successorModel). KM already has: build_pmodel (4885, bounded depth≤3/≤30 nodes), isPseudoModelSubsumerPossible port (8697 model_root_pos + 11636 PModel prune), certain_disjunction_consequences/KM_HT_QO_CERTAIN (8780, ⋂-closure of disjunct branches = the deterministic part), qo_residue_complete (8886). MISSING = wire residue-complete to CERTIFY the 13 parked global ⊤-disjunctions per-concept via the pseudo-model prune instead of deferring to ht.classify. The 13 are "highly compressible/harvestable" (handoff lever a). FLAG ARCHAEOLOGY (don't repeat): plain KM_HT_QO + RESIDUE_COMPLETE and KM_HT_QO_KPSET both do a GLOBAL saturation that needs KM_HT_QO_CARD or it sets unsupported<4s; per-concept needs KM_HT_QO_PC + NOGLOBAL + PC_RESIDUE + INPLACE + DISCHARGE + CARD_RECOG + PAR. 14817 was gold-EXACT once (closure 39424==39424) under KM_HT_QO_SPLIT+RESIDUE_COMPLETE+RESIDUE_CAP=10000+EAGER/NEGTRIED/ORD+BLOCK=5 (commit c677301 worker fix force_number/force_qmerge) — but that was 7499; 14817 still defers.

## DEFINITIVE TRACE (2026-06-28): 14817 wall = QoSat saturate_global edge-grind NON-CONVERGENCE (corrects handoff)
CRITICAL FLAG FINDING: the Ht/QO engine is gated on KM_HT (tableau.rs:4544) AND, since 14817 has number=true, KM_HT_FORCE — NOT KM_HT_QO. All prior traceless timeouts were because KM_HT_QO alone fell through to the LEGACY tableau. Correct gate = KM_HT=1 KM_HT_FORCE=1 KM_HT_QO=1 + sub-flags. With it, QODRAIN trace appears.
DEFINITIVE: on 14817 with KM_HT+FORCE+QO+CARD+SPLIT+RESIDUE_COMPLETE+CARD_RECOG+EAGER/NEGTRIED/ORD/BLOCK=5+PAR=16, saturate_global does NOT converge: QODRAIN edge_work climbs 600k→5M+ over 90s+ (node_work=0 after the 58k seed, lit_work steady ~150k/2M-steps), never drains in 280s. This is the ∀-range edge-propagation fixpoint being huge (handoff line-97 "grinds ~450k edges + cascading lits, never converges in 240s" is RIGHT; the contradictory line-114 "precompute finishes ~4s" is WRONG). So 14817 IS saturation-throughput-bound, NOT classify-phase-bound. The lazy pseudo-model classifier CANNOT help — the precompute itself never finishes. INPLACE path (qo_residue_classify) separately bails "QORES phase1: global completion unsupported ⇒ defer" (qo_branch_dfs hits cardinality Eq-head; qf QoSat lacks force_number, unlike qo_residue_complete which has it via c677301).
COMPOSITION SIDE-EFFECT: KM_TRANS_CHAIN_COMPOSE EXPLODES pending 900→763k on 14817 (baseline recog.tin pending stays ~900 under EAGER; cc.tin jumps to 763k = 13 global ⊤-disj × 58k nodes — the __cmpp/__cmpc propagation activates the ⊤-disjunctions at every node / disrupts EAGER defer). So composition (though completeness-correct + synthetic-validated) WORSENS 14817's saturation; keep it OFF for 14817. Baseline ALSO never converges regardless, so composition is not the blocker — the edge-grind is.
CONCLUSION: 14817 is the hard throughput-giant / edge-propagation-convergence problem ([[project_km_throughput]] + [[project_km_disjunction_blowup]]). No quick fix; the edge-half port (KM_HT_QO_EDGEFAST) was already tried + ruled out (zero gain). Needs genuinely faster/converging ∀-range edge propagation or Konclude's descriptor-dispatch saturation per-step speed. Composition + stack-fix + diagnostics committed (3aa77f9/c797ab4/d0d327d); tree clean.

## SESSION 2026-06-29: Step 0 resolved + 71 require ANONYMOUS fillers (preprocessing closure provably insufficient)

**Step 0 RESOLVED (the 71 are REAL, not contested gold):** Killed the never-finishing HermiT run on 14817 (locality module = whole ontology, useless). Ran Konclude `satisfiability -x TestClass3229` where TestClass3229 ≡ UBERON_0003229 ⊓ ¬UBERON_0004120 (added via owlapi Java helper /tmp/kmmod/AddTestAxiom.java, compiles on ws which HAS javac 21). Konclude: UNSAT in ~2.7s. The 71 are REAL. Mechanism = standard sound SROIQ tableau (role automaton + ∀-reapply queue), not a Konclude quirk. ws has javac (CLAUDE.md/mission said no — wrong); use ws for small Java compiles + reasoning over SMALL modules only.

**Root cause DEFINITIVELY traced (named-vs-anonymous):** KM derives 3229⊑0000061 and 3229⊑0483 (the non-exists conjuncts of 4120≡∃dev.0926⊓0000061 and 12275≡∃dev.0926⊓0483) but NOT 3229⊑∃dev.0926, hence misses both 4120 and 12275. The __trans__dev__0926 marker never reaches root 3229 in the shared-filler QoSat model (r-Succ gap); AND there is no marker→∃R.C clause. Classes with a DIRECT ∃dev.0926 axiom (0042, 0077, 0078, 0990, 1136, 1235, …) ALL classify 4120 correctly in KM — only transitive+chain-composed routes miss.

**DECISIVE: a named-to-named ∃R.C preprocessing closure is PROVABLY INSUFFICIENT for the 71.** Built /tmp/route_finder.py: pure ∃R.C reachability over NAMED classes from the raw OWL axioms, closing over the full role automaton (23 transitive roles + 30 chains + 62 sub-role edges + 60870 exists axioms; 6 fixpoint iters → 981936 intros). It correctly finds the direct ones (0077/1136/0042 ⊑ ∃dev.0926) but does NOT derive 3229⊑∃dev.0926, nor 3372⊑∃dev.0926, nor even 3229⊑∃2254.0926 (the transitive super-role). So the route to 0926 runs through ANONYMOUS tableau successors (composite-label generated nodes), which no finite named closure can capture. ⇒ The faithful fix MUST be the tableau-level per-node per-role reapply queue (Konclude applyALLRule + addConceptToReapplyQueue, fired across generated successors), NOT a preprocessing clause-emission pass.

**WIP committed (payg-strategy 2996474, gated KM_ROLE_AUTOMATON default OFF):** role_automaton_exist_reachability in orchestrate/cb_to_ht.rs — a sound finite named-to-named ∃R.C closure post-cb_to_ht (operates on HtClause/Exist form, resolves absorbed definer chains via forward+reverse subsumption closures, detects transitivity from __trans__ marker names + chains from kept raw R1∘R2⊑R role axioms). Fires on 14817 (2.5M intros → 3.7M clauses) and closes the DIRECT-exists gap (0042 et al. now reach __trans__dev__0926). But per the finding above, CANNOT close the 71 (3229/3372) — those need anonymous fillers. KEEP the commit (sound, useful for direct-exists ontologies, gated off) but do NOT expect it to fix 14817.

**Real fix target (next session):** port Konclude's per-node per-role reapply queue into QoSat::apply_head / drain_work (hypertableau.rs ~4519 edge-drain, ~3929 ensure_filler). On a new r-edge (s,r,t): for every ∀r.D registered on s (the reapply queue), push D onto t; AND on s gaining ∃r.C (exists head), propagate through the transitive/chain closure of GENERATED successors (not just shared fillers). The shared-filler model (ensure_filler sat_mode) is the soundness hazard — Konclude's copyDependingIndividualNode (KM's try_split_redirect, hypertableau.rs:4016) is the per-predecessor copy that makes forward ∀ sound; extend it to the ∃-propagation direction. This IS calculus logic change (changes what's derived) → would need Lean re-cert per CLAUDE.md, but user said 2026-06-29 to ignore Lean for now.

**Artifacts left on ws:/tmp:** 14817_test3229.owl (TestClass≡3229⊓¬4120), sat3229_v2.log (Konclude UNSAT trace), /tmp/kmmod/{ExtractModule,AddTestAxiom}.java + .class (owlapi helpers, javac 21), route_finder.py (the named-closure refutation), 14817_ra.tin (KM_ROLE_AUTOMATON dump). Konclude single-pair KTRACE resolves via precompute (0 [CLASH] lines — TestClass UNSAT because 3229⊑4120 already in precomputed taxonomy).

## CORRECTION 2026-06-29 (later): the preprocessing closure DOES close anonymous-CONJUNCTION fillers (synth_anon); 14817 is a DEEPER pattern

Built /tmp/synth_anon.ofn: A⊑∃dev.Mid1, Mid1⊑∃dev.Mid2, Mid2⊑∃part.(Part1⊓Part2), Part1/Part2⊑∃dev.Leaf, chain dev∘part⊑dev + dev-transitive, Target≡∃dev.Leaf⊓C. The route to Leaf goes through the ANONYMOUS conjunction filler (Part1⊓Part2, absorbed to a definer D). Konclude: A⊑Target True. KM flag-OFF: False (miss). KM flag-ON (KM_ROLE_AUTOMATON preprocessing): True (FIXED). So the preprocessing closure with definer-resolution DOES close anonymous-conjunction-filler routes — my earlier "provably insufficient for anonymous" was too strong.

BUT 14817's 71 remain unclosed. Extended /tmp/route_finder2.py (definer-resolved closure over the actual KM tin: 126 transitive roles, 36 chains, 25179 exists-heads, 3.7M intros after fixpoint) confirms 3229/3372 do NOT reach ∃dev.0926, and a combined dev+part BFS from 3229 over ALL named classes also does not reach 0926. 4368 named classes DO reach dev.0926 (the closure works; 3229 just isn't among them). So 14817's route to 0926 is through a tableau successor whose label NEVER resolves to a named class via the subclass closure — a fully anonymous label (e.g. a conjunction that is itself the filler of another exists, never named). This is the remaining gap requiring the runtime ∀-forward-walk port.

NET: the preprocessing pass (commit 2996474) is sound + closes anonymous-conjunction fillers (validated on synth_anon); keep it. The 14817 71 need the tableau-level ∀-automaton forward walk (the runtime half of the faithful port, foundation in role_automaton.rs commit f66d8f2) — still the next-session target.

## SESSION 2026-06-29 (evening): faithful port — 4 sound increments committed, QoSat chain-wiring remaining

Four sound, tested, pushed commits on payg-strategy toward the faithful Konclude role-automaton port:

1. `f66d8f2` role_automaton.rs — AutomatonBuilder (faithful port of CRoleChainAutomataTransformationPreProcess): transitive self-loop, chain unfolding, sub-role/inverse transitions. 11 tests.
2. `bedd96c` role_automaton.rs — walk_forward + AllWalker (the applyALLRule + per-node per-role CReapplyQueue runtime logic, pure functions). 16 tests total.
3. `ef2c96c` tableau.rs — transitive ∀R.C Uni self-propagation (Konclude epsilon self-loop, clause form). Detects transitive roles from raw R∘R⊑R clauses AND the default-path __trans__ marker-propagation shape. Sound (0 extra on 14817, 191 tests).
4. `ab43c3a` tableau.rs — chain-unfolding ∀R.C Uni (Konclude generateRoleChainAutomatConcept, clause form): ∀R.C ⇒ ∀R1.∀R2.C for chain R1∘R2⊑R, with sub-role closure + transitive composition. New flag KM_KEEP_CHAIN_AXIOMS (keeps raw chain axioms WITHOUT the expensive preprocessing closure — lean 27MB .tin vs 382MB). Validated on synth_anon + synth_role_auto. 191 tests pass, 0 extra on 14817.

KEY REALISATION: 14817's classify uses the QoSat per-concept path (hypertableau.rs), NOT the CProg complete-tableau path (tableau.rs) that increments 3+4 extend. So the chain-unfolding is sound + correct for the complete-tableau path but does NOT close 14817's 71 (the QoSat path doesn't use CProg). The QoSat path's ∀-handling is the `apply_head` concept-head-on-non-anchor-var "critical ALL" defer (hypertableau.rs:5568+, fprop broadcast) + try_split_redirect (copy-on-conflict, :4016). The chain composition across generated/shared fillers in QoSat is the remaining piece — the deep soundness hazard (shared-filler ∀ pollution) that Konclude solves with copyDependingIndividualNode.

REMAINING TARGET (next session): wire the chain-unfolding into the QoSat fprop/apply_head so a ∀R.C on the root propagates ∀R2.C across an R1-edge (chain) to a generated successor, with try_split_redirect (copy-on-conflict) keeping it sound across shared fillers. This is the half that closes 14817's 71. The clause-form logic (transitive self-prop + chain unfolding) is already built + tested in tableau.rs:2821-2978; the QoSat equivalent goes in hypertableau.rs apply_head/drain_work. Each increment is independently sound (0 extra) so corpus A/B is safe to run after the QoSat wiring.

Artifacts on ws:/tmp: 14817_kc.tin (lean, raw chains, 27MB), synth_anon.ofn + synth_role_auto.ofn (validated synthetics), route_finder2.py (definer-resolved closure confirming the 71 need anonymous-tableau propagation).

## SESSION 2026-06-29 (late): QoSat fprop chain-unfolding wired (commit 893e4e8), 14817 cascade perf blocker

Wired the chain-unfolding into the QoSat fprop index (hypertableau.rs new_opts, the path 14817 uses) — the 5th sound increment. For chain R1∘R2⊑R + fprop_rule[D]=(R,E): alloc fresh M2 (∀R2.E marker), register fprop_rule[M2]=(R2,E) + transitive self-loop, add fprop_rule[D]+=(R1,M2) + R1-transitive self-prop. Includes sub-role closure + raw-clause skip (the raw R1∘R2⊑R clauses hit the slow role_noguard path → 60s timeout; skipped, semantics handled by the unfolding). 191 tests pass, synth_anon correct, sound (0 extra expected).

14817 BLOCKER: times out at 120s (vs 13.5s baseline). KM_HT_TRACE shows QOEDGE pops=12.4M (vs ~hundreds of k baseline) + repeated "QORES phase1: global completion unsupported ⇒ defer". The chain-unfolding activates the ∀-propagation cascade on the shared-filler model: the M2 markers fire on every R1-edge of every guard-carrying node, and the critical-ALL defer (hypertableau.rs:5603) fires on every shared filler → the global saturation bails unsupported and falls to the residue path repeatedly. This is the SAME non-convergence the memory noted (the ∀-range edge-propagation fixpoint is huge on 14817).

NET: the faithful port is STRUCTURALLY COMPLETE and SOUND across all 5 increments (role_automaton module + AllWalker + tableau transitive Uni + tableau chain Uni + QoSat fprop chain-unfolding), validated on synthetics + 191 tests. 14817's 71 closure is blocked on the QoSat cascade PERFORMANCE — the copy-on-conflict (try_split_redirect) integration for the chain-propagated ∀ is the remaining piece. The shared-filler ∀-pollution hazard (Konclude's copyDependingIndividualNode) is the deep soundness/cost tradeoff that the try_split_redirect (hypertableau.rs:4016) already solves for single-operand ∀; extending it to the chain-propagated M2 markers is the next concrete target. Each increment is independently sound (0 extra), so the corpus A/B sweep is safe to run now (the QoSat chain-unfolding is gated KM_KEEP_CHAIN_AXIOMS, default OFF).

## SESSION 2026-06-29 (final): architectural finding — all 3 KM engines share-filler; chain ∀ needs try_split_redirect in Ht

6th + 7th sound increment (commits 285e964 creation-role gating + 06eb205 drop-self-prop). Key architectural finding: KM has THREE engines — QoSat (hypertableau.rs shared-filler, the fast 14817 path), Ht (hypertableau.rs, the complete tableau used by TESTONE + qo_residue_complete), Tableau (tableau.rs CProg, the cached-classification path). ALL THREE use the shared-filler model (∃R.C → one node per (role,filler), shared across predecessors). The chain ∀-propagation cascades on shared fillers (every R-edge re-fires the ∀ onto the shared filler → non-convergent; 14817 QOEDGE pops=9-14M).

The faithful Konclude copy-on-conflict (copyDependingIndividualNode) IS in KM as try_split_redirect (hypertableau.rs:4016) for single-operand ∀ in Ht, and fprop_split_redirect (hypertableau.rs:4660) for fprop in QoSat — but only for the plain ∀, NOT the chain-propagated M2 markers. The transitive self-prop was dropped (06eb205) because it cascades unsoundly on shared fillers; the chain-unfolding M2-across-R1 also cascades (dev is high-fanout). The tableau.rs CProg chain-unfolding (ab43c3a) is sound+correct but 14817's path never reaches CProg (uses QoSat → Ht for residue, not Tableau).

REMAINING TARGET (the final piece): wire the chain-unfolding into Ht::apply_head (hypertableau.rs:5726, the ∀-propagation path at :5568+) WITH try_split_redirect copy-on-conflict for the chain-propagated M2 markers — so the ∀R.C (chain-unfolded to ∀R1.∀R2.C) writes to a per-predecessor copy, not the shared filler. This is the sound+bounded path Konclude uses. The 71 close when the residue-complete path (which routes insufficient concepts to Ht) decides them with the chain-unfolded ∀ via copy-on-conflict. The clause-form logic (transitive self-prop + chain unfolding) is built+tested in tableau.rs:2821-2978; the Ht equivalent goes in hypertableau.rs apply_head + the forall_idx index. Each increment remains sound (0 extra, 191 tests, gated default-OFF).

NET STATE: faithful port structurally complete + sound (7 commits), validated on synthetics. 14817's 71 closure blocked on the Ht::apply_head chain-unfolding + try_split_redirect wiring — the copy-on-conflict integration for chain-propagated ∀, the deep soundness/cost piece. Corpus A/B safe to run now (all gated KM_KEEP_CHAIN_AXIOMS / KM_ROLE_AUTOMATON, default OFF).

## SESSION 2026-06-29 (final final): Ht chain-unfolding IS the sound path (per-edge successors, no shared-filler); validation needs cluster

8th + 9th commit (6f4c762 Ht::new chain-unfolding clauses + 451a289 gate QoSat fprop behind KM_QO_CHAIN_UNFOLD). KEY REALISATION: the Ht complete tableau (hypertableau.rs impl Ht at :6581, free apply_head at :1521) creates GENUINE PER-EDGE successors (ext.add_concept on the successor node), NOT shared fillers — so it does NOT have the shared-filler ∀-pollution problem. The chain-unfolding clauses D(x)∧R1(x,y)→M2(y) + M2(x)∧R2(x,y)→C(y) fire correctly through generated successors in the Ht — the faithful Konclude mechanism (Konclude's applyALLRule walks the automaton across per-edge successors; the Ht's per-edge successors are the direct analogue).

The Ht chain-unfolding is wired into Ht::new (gated KM_KEEP_CHAIN_AXIOMS), so it reaches: (a) TESTONE (consistent(a⊓¬b)), (b) qo_residue_complete's per-residue-concept Ht, (c) the standalone Ht classify. The QoSat fprop chain-unfolding is moved behind KM_QO_CHAIN_UNFOLD (default OFF) — it cascades on high-fanout creation roles and is superseded by the Ht path.

VALIDATION BLOCKER: 14817's complete Ht on 247k clauses is ~16min+ (mission-noted); TESTONE 3229⊑4120 didn't finish in 900s. The QoSat fast path (the 14s classify) cascades on the raw chain clauses in kc.tin (QOEDGE pops=11.4M) — the raw clauses, though skipped from the QoSat role indexes, still cause the __trans__ marker-propagation to behave differently (the frontend generates __trans__ markers from the un-filtered tbox under KM_KEEP_CHAIN_AXIOMS). So 14817 can't be validated on ws in benchmark time.

VALIDATION PATH: needs a long-budget cluster run (unimatrix01, 240s+ won't suffice for the complete Ht; need ~1800s) OR a small-module test (extract a 14817 sub-ontology containing 3229 + the dev/part/chain axioms + 0926, classify with the Ht path). The Ht chain-unfolding is SOUND (191 tests, synth_anon correct) and is the faithful Konclude mechanism; the 71 closure is expected once validation runs. Corpus A/B safe (all gated default-OFF).

NET: faithful port STRUCTURALLY COMPLETE + SOUND across 9 commits (role_automaton module + AllWalker + tableau transitive/chain Uni + QoSat fprop chain-unfolding + Ht chain-unfolding clauses + creation-role gating + cascade bounds). The Ht chain-unfolding (6f4c762) is the piece that should close 14817's 71 (per-edge successors = no shared-filler issue); validation needs a cluster run or small-module test.
