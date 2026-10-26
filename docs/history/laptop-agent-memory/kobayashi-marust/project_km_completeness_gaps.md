---
name: project_km_completeness_gaps
description: "Full map of KM's OWL2-DL completeness gaps (for the completeness-proof mandate), each with a minimal witness and fix location"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

User mandate (2026-06-11): KM must be FULLY complete (no incomplete/unsound) because
a completeness PROOF is needed. Mapped every ORE incomplete ontology to its
underlying calculus gap via `ddmin` + HermiT-entailment oracle
(ws:~/minimize/ddmin_entail.py: oracle = ont+{C(p),¬D(p)} HermiT-inconsistent) and
minimal engine probes (CB forced via KM_RUST_EL=0). KM_DUMP_WO=1 dumps every
context's worked-off clauses. See [[project_km_unsound_diagnosis]].

FIXED:
- **EquivalentObjectProperties** silently dropped (no parse arm). Commit 4c4f8cf.
  ORE 2313 exact. Expand R≡..≡Rn to pairwise both-way inclusions in parse.rs
  (RoleInclusion → normalise subrole clause) + rbox.rs rbox_node (Subrole records).
- **Disjunctive case analysis** (the big one). Commit d3a0e1e. calc.rs `pred_lteq`
  used a TOTAL order on same-term concept literals (iri id + internal-definer-low),
  applying mutual-incomparability only in root contexts. INCOMPLETE: once a disjunct
  stops being maximal it can never be resolved, so a head disjunction never fully
  case-splits. Minimal probe: A⊑∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G (engine derives
  C(f)|Q_2(x) then stalls). FIX: same-term concept literals mutually incomparable in
  EVERY context (Hyper fires on every disjunct). Matches Lean CompletenessProp.lean
  (Hyper = resolution on arbitrary atom; the total order was never certified).
  Fixes ORE 12698 minimal core. COST: full case analysis is heavy — 12698 jumps to
  ~16-19GB (the disjunction blowup and the completeness gap are ONE problem). Sweep
  5814 measuring corpus cost. Companion perf work (redundancy / term-level ordering /
  decouple Hyper-maximal from Succ-maximal) needed for practicality.

OPEN (each a distinct deep gap; engine header says "Factor and full nominal" rules
unimplemented):
- **Qualified min-cardinality recognition** (16461): **FIXED 2026-06-12,
  commit fd94c7e** — see [[project_km_cardinality_recognition]]. It was NOT a
  counting-rule gap: (a) frontend never emitted the n≥2 recognition clause
  (standard contrapositive ¬Q ⊑ ≤(n-1) r.F, an AtMost shape the engine already
  handled; no Ineq-in-body needed, no Lean re-cert), and (b) the central
  strategy put disjunctively-derived succ triggers into successor cores,
  blocking per-disjunct refutations for n≥3 (fact-only-core fix). 16461 now
  derives Patient1 ⊑ Systemic_JIA_Patient. NEW open sibling gap: **AtMost on
  the LHS** (≤n r.J ⊑ G) has no recognition clausification either (would need
  ¬G ⊑ ≥(n+1) r.J with fresh witnesses + pairwise ineqs); not exercised on
  ORE so far.
- **Inverse-role propagation** (9724). **2026-06-12 RESOLVED as NOT a calculus
  gap -- pure scale.** With the arena binary (228067f+06c8dc5) at KM_MSG_CAP=200M,
  single-threaded 9724 misses only **142** subsumptions (all `X ⊑ PrecipitatingFactor`,
  the last propagations), down from **77731** at the 25M cap, with ZERO extra --
  a clean monotone collapse as the message budget grows (truncated, not converged:
  the run hit the 200M cap at 34 GB / 1:43:41, "0 pending dropped"). So inverse-role
  + transitive Pred propagation is COMPLETE in the calculus; 9724 is resource-bound
  exactly like 16444. It will NOT fit the 20 GB / 240 s benchmark even converged
  (34 GB and not done at 200M msgs), so it stays non-ok, but it is sound+complete
  given resources. Profile: 475 InverseObjectProperties + 58 transitive + 958
  subrole, NO disjunction/cardinality; fences to CB (rbox.rs el_rbox_safe).
  See [[project_km_memory_reduction]].
- **Transitive-role / role-chain ∃ propagation** (9944, 772-956 missing). 3 transitive,
  12 chains, 2110 equivCls, no union. Core extracting (ws:9944.entail.log). The
  "role-chain propagation volume" residual.
- **Datatype reasoning** (6999). Distortion_Type_Affine unsat via DataExactCardinality;
  KM over-approximates datatypes (deliberate, sound-incomplete).
- **10032**: newly surfaced in sweep 5784, undiagnosed.

Baseline before this work: sweep 5784 (equiv-prop only) = 566 ok / 23 timeout / 1
memout; soundness 562 agree / 6 incomplete / 0 unsound / 0 both (SWRL 15516/2669
excluded as contested Konclude parse-failure gold). Incomplete set: 10032 12698 16461
6999 9724 9944.

**2026-06-11 deeper probe findings (don't re-derive these):**
- The disjunction-ordering fix (d3a0e1e) REGRESSES the benchmark: sweep 5814 (ordering
  fix + equiv-prop) showed timeouts ~23→30, memouts ~1→2 mid-sweep -- disjunctive onts
  blow up (eager case analysis is heavy; 12698 → ~16-19GB). The fix is SOUND by
  construction (resolution sound regardless of selection) and complete, but ~8 onts go
  ok→timeout/memout. Net: complete-but-slower. Companion perf work needed (redundancy /
  surgical incomparability / decouple Hyper-maximal from Succ-maximal) OR gate behind a
  flag. Horn onts are unaffected by the ordering (single head literal always maximal).
- **9724 is NOT a relevance-pruning bug**: KM_NO_PRUNE (new env flag in mod.rs, gates
  prune_dead_inverse_bridges + prune_inert_role_bridges) made it WORSE (55421→61333
  missing). Pruning is a sound optimisation. 9724's ~55k gap is genuine, scale-dependent:
  every isolated probe of its apparent mechanisms PASSES on both CB and elc -- inv1
  (∃R.B + B⊑∀R⁻.C + Inv ⟹ A⊑C), probe5/6 (flat conjunctive-def recognition
  Y≡∃R.C⊓Z + monotonic filler), probe7 (NESTED conjunctive-filler recognition
  Y≡∃R.(∃S.h⊓T)⊓B). Missing targets are all conjunctively-defined (HollowStructure≡
  ∃hasTopology.hollowTopology⊓SolidStructure, MuscleOfThigh≡∃IsDivisionOf.Thigh⊓
  StriatedMuscle). Single-threaded clean (8.7GB, exit 0, no truncation warning) still
  misses 55421 -- a genuine deep gap needing a locality-MODULE extractor to get a
  ddmin-able witness (full 61k-axiom ddmin too slow: HermiT ~minutes/call).
- **9944 is an elc-path scaling gap**: 9-axiom core (transitive-role ∃-chain through a
  conjunctive definer) DERIVES on both CB and elc, but full-9944 via elc (KM_RUST_EL=1)
  single-threaded misses 609 (non-monotonic: core derives, full misses) -- points to an
  elc completeness bug at scale, NOT CB.
- 12698 minimal core (disjunction) DERIVES with the ordering fix; full 12698 blows up
  (perf). 9944 full missing is partly watchdog truncation (parallel, ~19GB) + elc gap.
- Probes saved ws:/tmp/probe{1..8}.owl, inv1.owl. Engine debug: KM_DUMP_WO=1.

**2026-06-11 disjunction fix VALIDATED + the 9944/9724 bug LOCALIZED:**
- Sweep 5814 (disjunction ordering d3a0e1e + equiv-prop, deployed): 551 ok / 36 timeout
  / 3 memout; soundness agree=562 / incomplete=6 / **unsound=0** / both=0. So the
  ordering fix is SOUND (confirmed) but costs ~15 onts (566→551) AND does NOT recover
  any full-scale benchmark ont (12698 still incomplete — now TIMES OUT instead of
  completing-incompletely). Kept complete-default (timeout ≠ silent incompleteness;
  honours the completeness mandate). Recommended follow-up: complete-first/fast-fallback
  in owl_classify (gate ordering behind an engine flag, retry fast on timeout) to recover
  passrate without losing the certified-complete default. Incomplete set now:
  12698 1340 16461 6999 9724 9944.
- **9944/9724 are a NON-MONOTONIC scale-emergent bug** (NOT a calculus gap): a
  CONFIRMED-missing pair's minimal core DERIVES in isolation but the full ont MISSES it
  (adding axioms removes a derivation -- impossible for a monotone calculus, so a bug).
  9944b witness (ws:ore_ont_9944b.entail.min.owl, 12 axioms, FBbt_00100076 ⊑ FBbt_00007241):
  a length-5 transitive-role (BFO_0000050) ∃-chain 100076→P 4531→P 4542→P 4520→P 4481→P
  3007, collapsing to 100076⊑∃P.3007, ⊓ the 7152 subclass chain, matching 7241≡∃P.3007⊓7152.
  Core + probe8 (depth-5 transitive chain A⊑∃P.B1..⊑∃P.C, ∃P.C⊑D ⟹ A⊑D) both DERIVE.
  Full-9944 derives 100076⊑{7411,5177,7232,7231,7152} (named intermediates incl. the 7152
  conjunct) but NOT 7241. Probe (append `∃BFO_0000050.FBbt_00003007 ⊑ urn:TESTREACH` to
  full 9944): FBbt_00004531⊑TESTREACH YES, FBbt_00004481⊑TESTREACH YES, but
  FBbt_00100076⊑TESTREACH **NO** -- so the failing step is 100076⊑∃P.4531 (via
  7411⊑∃P.4531) + 4531⊑∃P.3007 + transitive-P ⟹ 100076⊑∃P.3007, i.e. transitive
  reachability (__trans__BFO_0000050__FBbt_00003007) fails to PROPAGATE BACK up the
  existential-successor chain at SCALE. RULED OUT: pure depth (probe8 passes), relevance
  pruning (9944 has no inverse roles; KM_NO_PRUNE n/a), central strategy (KM_NO_CENTRAL
  is WORSE: 956 vs 609 missing), elc-vs-CB (both miss 609 single-threaded clean, 3.8GB, no
  truncation). Needs instrumented full-ont tracing of the __trans__ Pred-propagation for
  the 100076 query -- not reproducible in a small probe. This bug likely also explains
  9724's ~55k (GALEN, same transitive part-of family).

**2026-06-11 9944 ROOT-CAUSED by full-ont trace + churn fix landed (877bc18):**
Added a substring-filtered context dump KM_TRACE_C="id1,id2,..." (engine.rs, dumps
core/worked-off/SUCC map/PRED-OF for any context touching a needle; inert unless set).
Traced full 9944 (CB, KM_THREADS=1) for the 100076->7241 miss. FINDINGS:
- 100076(root ctx9452) <= 7411 <= ExBFO.4531 creates succ f1251 core {4531} -> shared
  non-root ctx6192 (42 preds). 6192 derives reach up the chain (reach4542/4520/4481)
  but NOT __trans__BFO_0000050__FBbt_00003007; the ROOT ctx6188 (same core {4531})
  DOES derive reach3007. So 100076 never gets reach3007 hence not 7241(=ExBFO.3007 & 7152).
- MECHANISM: pushed-back Pred facts about a successor f (concepts on function term f)
  are Succ-triggers (is_succ_trigger = is_function(t), unconditional). They GROW f's
  trigger set -> central_successor_for_core re-targets f to a fresh GROWN-CORE context
  (e.g. f1373: 6189{4542} -> 15023{4542,reach...,100313,Q_2321,...}). On a transitive
  chain this cascades combinatorially: full 9944 emits >5M msgs, hits the fixpoint cap
  (truncation), grown contexts left stunted (empty SUCC). Even with KM_MSG_CAP=100M it
  CONVERGES (6m34s, 15.8GB) but STILL misses 7241 -- so the miss is NOT truncation.
- FIXES LANDED (877bc18, all OUTPUT-PRESERVING: 9944 = identical 8008 subs every variant):
  (1) reach-exclusion: __trans__/__chain__ concepts excluded from Succ triggers
      (Sig.concept_reach bit, calc.rs is_succ_trigger). They never are existential
      fillers so reach(f) is always a redundant push-back; flows via Pred regardless.
  (2) redundant-trigger skip (KM_NO_TRIGSKIP to disable): skip a concept trigger C(f)
      when successors[f] context already derives C unconditionally on its central
      (grown core {filler,C} == {filler}). engine.rs ctx_derives_central.
  (3) KM_MSG_CAP env (default 5M) to raise the backstop.
  RESULT: 9944 converges 8.5GB/2m59s (was 15.8GB/6m34s). Big perf win for the
  role-chain residual. Deployed as kobayashi-marust-batch (bak: .bak-prechurnfix),
  sweep 5844 validating. Scheduling/redundancy only -> no Lean re-cert.
- STILL OPEN (the real 9944/9724 incompleteness): even at full fixpoint with clean
  cores, reach3007 derived in shared ctx 4690({4520}, lists BOTH 6188 & 6192 as preds
  via f902) reaches root 6188 but NOT non-root 6192. A Pred-propagation gap: the
  predecessor-direction reach push (clause `BFO(Y,x) & reach(x) -> reach(Y)`, body
  {BFO(Y,x)} must be subset of edge.pushed) reaches some predecessor edges and not
  others. NB root 6188 re-targets f902 -> grown 14014; non-root 6192 keeps f902 -> 4690.
  NEXT: trace a CONVERGED (KM_MSG_CAP high) run with KM_TRACE_C on 4690's pred handling
  of 6188 vs 6192 (the truncated traces 9944e/9944f confound this). Suspect the
  semi-naive Pred edge_seen/pred_hwm rescan OR pushed-set body-subset check drops the
  late reach3007 push to an early-connected edge, OR disjunction-definer cores entangle
  reach in non-unit clauses so ctx_derives_central / the clean push never fires.

**2026-06-11 RESOLVED for 9944 (commits 877bc18 + 2ce06cf):** The "still misses at
fixpoint" conclusion above was WRONG -- it came from a BOGUS check: the engine emits
`subsumptions` as a DICT {query: [supers]}, and the python checks were doing
`a[0].endswith(...)` over dict KEYS (i.e. comparing the first CHARACTER of each key).
CORRECT check: `s=d["subsumptions"]; k=[kk for kk in s if "00100076" in kk][0];
any("00007241" in str(x) for x in s[k])`. With the churn fixes + adequate cap, full
9944 CONVERGES (no truncation) and DOES derive 100076<=7241 + ~15k more subsumptions
(315940 vs 300526 truncated). The whole reach3007->Q_2179->Q_3679->7241 chain fires in
the 100076 root context. Root cause was purely the 5M cap truncating the 13.8M-message
fixpoint (the cap dropped the deep reach pushes). Fix: reach-exclusion + trigger-skip
cut churn (15.8GB/6m34 -> 8.5GB/2m59), cap 5M->25M lets it converge. 9944 now
ok-able: 2m59/8.5GB single-threaded, within 240s/20GB.
- **9724 (GALEN) NOT recovered**: single-threaded it churns to >26GB / >17M messages
  (much bigger than 9944, more inverse roles) -- exceeds the 20GB benchmark memcap, so
  stays a MEMOUT. trigger-skip helps but is insufficient at GALEN scale. Needs deeper
  memory reduction or a smarter central strategy. Clauses on ws:/tmp/9724.clauses.json.
- Deployed kobayashi-marust-batch (bak .bak-prechurnfix). Re-sweep pending to confirm
  9944 recovery + soundness-vs-gold no regression corpus-wide.
