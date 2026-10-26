---
name: project_km_shiq_build
description: 2026-06-24 building the real sound SHIQ-completion (Path 2) for the throughput family; P2.1 done, crux = saturation cache + incremental mode-3 blocking
metadata:
  node_type: memory
  type: project
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

User directive (2026-06-24, emphatic): build the REAL + COMPLETE SHIQ-completion
sound shared-saturation architecture in KM (`saturate_global` with non-shared/blocked
successors + cardinality merge + disjunction convergence), tracing Konclude, NO
shortcuts. Target = solve the 9 throughput onts
(10908/14817/10621/7499/7914/3215/9663/9724/15672) sound+complete+fast (<150s).
Defer Lean to the very end ([[feedback_lean_at_end]]).

**SESSION 8 (2026-06-26) — lever-C empirical diagnosis on 9724 (ws, KM_HT_TRACE),
overturns the "inverse over-defer" framing; committed KPWRITE + KM_NO_INVCOMPOSE +
test on payg-strategy.** Measured the ACTUAL classify blockers on ore_ont_9724
(SHIF; 23136 named, 14115 ∃-heads, 674 eq-heads, 0 disj) in the qo_candidate path:
1. FIRST wall is CARDINALITY not inverse: a functional/≤n `Eq`-head bails the pass
   `unsupported=true` at apply_head:4474 UNLESS **`KM_HT_QO_CARD`** (card_defer). The
   qo_candidate env (race.rs:586) does NOT set it — add it first.
2. With card_defer: `unsupported=false`, forward pass completes, **clean_subs=456239
   of gold 457090 (99.8%) SOUND** already; only ~851 subs need completion. BUT
   `kp_miss=66,661,218` (`inv_edges=2.5M`) ⇒ 20321/23136 concepts "affected" ⇒ defer.
3. **KPWRITE (sound backward-∀ self-node write, Konclude applyALLRule:6143, committed
   this session) does NOT fire on 9724** — kp_miss byte-identical with/without it. The
   66M misses are FILLER-targeted (writing+reading as named subsumers is the 7581
   conflation kpwrite correctly refuses). Sound but inert here.
4. INVCOMPOSE on/off (`KM_NO_INVCOMPOSE`): kp_miss 66.7M vs 65.9M — not the lever.
⇒ 9724 path = `card_defer` + **port #2: per-creation-role ALL-concept extension**
(operands in a separate per-(successor,creation-role) store, checked there not against
the conflated shared filler label, so the 66M filler-inverse checks PASS and the
affected set collapses). docs/LEVER-C-CACHE.md has the numbers. KPWRITE gated
KM_HT_QO_KPWRITE (implies sat_mode), locked by kpwrite_backward_forall_certifies_self_node;
151 tests pass. Sweep 7419 (SHOQ default-on) = 572 ok / 15 timeout / 0 unsound; NOTE
7581+16444 regressed to timeout (SHOQ promotion changed routing — investigate).
Konclude disjunction-family (1603/541/9540/12653) wins by satisfiable-EXPANDER/
pseudo-model cache reuse + small per-test completion graphs (~100-2200 nodes,
few-hundred backtracks), NOT saturation alone; 9540 hardest (4.9s, 438k OR-branches).

**Blueprint: docs/SHIQ-COMPLETION-DESIGN.md** (committed). Built from a 3-agent
Konclude trace (all file:line in the doc):
- ∀ = forward over GENUINE r-edges into INDEPENDENT (non-shared) successors
  (`applyALLRule` 16297) — this is why Konclude's ∀ is sound and QoSat's shared
  fillers are not.
- Blocking = optimized subset B1∧B2 (`isLabelConceptOptimizedBlocking` 18484): B1
  label⊆blocker, B2 parent carries blocker's ∀r-operands; dynamic/ancestor.
- ≤n merge `mergeMergingIndividualNodes` 15095 + choose-rule
  `qualifyMergingIndividualNodes` 15675; ≥n `createDistinctSuccessorIndividuals`
  16140. **KM's own Ht lacks the n≥2 ≤-merge** (apply_head:1025 → unsupported).
- Disjunction: `planORProcessing` 16489 DELAYS branching until live-disjuncts
  minimal; `executeORBranching` 16737 semantic; 3-phase dependency-directed
  backtrack `backtrackFromTrackingLine` 6963 + nogood cache.
- Saturation/tableau SPLIT: `CCalculationTableauApproximationSaturationTaskHandle`
  does all deterministic rules + caches results; tableau handles ⊔/choose residue.

**KM reuse map** (agent): `Ht::consistent(seed)` 5555 builds a per-concept
non-shared blocked completion (seed=[pos(A)] or [pos(A),neg(B)]); `set_fast_tableau`
4419; `compute_blocked` 4531 (mode 3 pairwise = sound for inverse, set via env
KM_HT_BLOCK=3); `merge_into` 622; dfs/backjump 5403/5513; KM_HT_NUMBER read in
Ext::new 338. QoSat ∀-pollution site apply_head ~3873 (critical-ALL), Eq cardinality
~3922; affected-set partition via `kp_insuff_nodes` bidirectional reachability.

**LANDED 2026-06-24 session 4 (payg-strategy, validated on IBEX):**
- **P2.2 qualified ≤n merge (commit 88ad148, gated KM_HT_QMERGE / `set_qmerge()`):**
  the complete Ht bailed `unsupported` on any AtMost head with ≥2 Eq disjuncts
  (n≥2 qualified ≤) → incomplete. Now a real ≤-rule merge BRANCH: apply_head
  pushes a trail-ordered `MergeDisj` (pure-Eq head; mixed concept+Eq i.e. negative
  ≥n recognition still bails sound); `branch_merge` tries each candidate pair
  (mark/merge_into/recurse dfs, backjump, accumulate fail), discharged at the dfs
  Scan::Sat fixpoint so cascades re-branch; distinctness `⊥⟵Eq` clauses reject
  illegal merges. eqdiag proved NEEDED by 7914 (23 multi-eq heads), 9663 (14),
  14817 (33); 9724/7499 functional-only, 3215 no cardinality. 2 new unit tests
  (≤2 SAT-needs-branch, ≤2 UNSAT-all-clash) + suite 133/0.
- **Incremental pairwise mode-3 blocking (commit 2ed7fbd):** mode-3 recomputed the
  (core(n),core(pred),edge-roles) signature O(n)/pass; now i3_recompute does the
  i2-style suffix recompute (shares i2_lo; add_edge widens suffix via `block3`
  since the sig uses the parent edge); shared `i3_signature` makes full+incremental
  identical by construction; KM_HT_INCRBLOCK2_CHECK extended to mode 3. 90s CHECK
  on 7914 real data = 0 mismatches. Per-build speedup (helps 7914/9663/14817/9724).
- NOTE: both are completeness/per-build-speed; NEITHER fixes the per-concept MODEL
  COUNT. qmerge gold-VALIDATED on 16461 (real ORE, number=true: 156/156 subs, 0/0).

**RE-CORRECTION (session 5 LATE, 2026-06-25): the `inverse` TInput FLAG IS
MISLEADING — 10908 (and the family) DO have inverse roles, encoded as BRIDGING
CLAUSES, with inverse=False.** role40 analysis (job 47777729): cid=1304
`BFO_0000083(x,y) -> BFO_0000123(y,x)` is an inverse-role axiom (BFO_0000123 =
inv BFO_0000083 = located-in / location-of). So the original "inverse-bound"
diagnosis was RIGHT; the session-5 "SHOQ inverse-free" reading below was WRONG
(it trusted the inverse=False flag). cb_to_ht sets inverse=False yet emits inverse
bridging clauses (`r(x,y)->rinv(y,x)`) — do NOT trust the flag; grep clauses for
reversed-variable role heads. 10908's false-UNSAT = inverse-edge propagation makes
node 1 a BFO_0000123-target → range(BFO_0000123)⊑BFO_0000006 forces +3, clashing
with Q_50⊑¬BFO_0000006 (cid 180) ⇒ spurious clash. This is the INVERSE+range+
disjoint soundness problem (the hard inverse frontier), NOT a quick cb_to_ht fix.
The fast Ht's bridging-clause inverse handling over-derives here.
CONFIRMED NOT a cheap fix (jobs 47777767/47777787): 593 stays UNSAT under the
FULL arsenal (EAGER+BLOCKSKIP+NEGTRIED+ORD+WATCH+PICK) AND with number off — so
it's a DETERMINISTIC clash, not search/number-resolvable. cid=1513 RAW =
`BFO_0000123(s,t)->BFO_0000006(s)` = DOMAIN(located-in)⊑spatial-region on the
SOURCE; domain/range are INTERNALLY CONSISTENT with the inverse pairing
(domain(located-in)=range(location-of)=BFO_0000006; range(located-in)=
domain(location-of)=BFO_0000004) → NOT a cb_to_ht swap. Mechanism: node 1 gets an
incoming location-of edge → inverse bridge cid1304 makes it a located-in SOURCE →
domain cid1513 forces +spatial → clashes with Q_50(=BFO_0000004⊓¬BFO_0000006,
cid181). Gold has 593 SATISFIABLE (it's a subsumee in gold, not in #UNSAT; KM's
unsat shows as "missing" subs not "extra"), so KM is UNSOUND here. A sound inverse
reasoner avoids forcing node1 to be a located-in source; KM's deterministic
bridging-clause inverse propagation does not. ⇒ 10908 needs SOUND INVERSE-AWARE
reasoning (the multi-session engine), confirming the ORIGINAL inverse-bound
diagnosis. NO sound same-session fix; refused to hack (soundness mandate).
DECISIVE ARBITER UNAVAILABLE (job 47777880): `km classify` 10908 via the
Lean-certified CB engine (the sound core, KM_HT off) TIMES OUT at 1200s (20 min) —
so no sound KM reasoner finishes 10908 in budget; bug-vs-contested for 593 cannot
be settled inside KM (would need HermiT, the contested-gold tiebreaker, which isn't
runnable here). NET: 10908 is hard for BOTH CB (sound, 20min timeout) and forced-HT
(fast but unsound/suspect false-UNSAT). All three targets are inverse-bound and
need the fast sound inverse-aware engine + disjunction convergence (multi-session);
this is re-confirmed, not a same-session solve. Session-5 net deliverables: nominal
o-rule committed (38cf4c9, 135 tests); inverse-flag-unreliable finding; 15672
model-fold (EAGER+BLOCKSKIP); 10908 unsoundness located to inverse+domain (clauses
180/181/1304/1513).

**[OUTDATED] CORRECTION (session 5, 2026-06-24): 10908 + 15672 are NOT inverse-bound — they
are SHOQ (nominals + number, inverse=FALSE in the clausified TInput; the frontend
eliminates the inverse roles).** probe3 (job 47776265): 10908 nominals=[18 ids]
inverse=False number=True, 1582 cl / 692 q, gold 6001 subs CONSISTENT; 15672
nominals=[3 ids] inverse=False number=True, 856 cl / 82 q, gold 142 subs
CONSISTENT. BOTH currently TIMEOUT (rc=124) on the legacy Tableau (the only route
with nominals). The earlier "nominal+inverse → fenced" claim was wrong: fencing
only fires when inverse_pairs is non-empty, and for these the post-clausification
inverse set is EMPTY. So both are reachable with the fast Ht once it has the
nominal o-rule + the ≤n qmerge (already landed) — NO inverse, NO NN-rule.

**SESSION 5 DEEP DIAGNOSIS (2026-06-24) — the two walls for 10908/15672, both
PRE-EXISTING fast-Ht limits, NOT caused by the nominal port:**
- **15672's model EXPLOSION was the deferred-disjunction-on-every-node issue,
  FIXED by EAGER+BLOCKSKIP (job 47777116):** with
  `KM_HT_EAGER=1 KM_HT_BLOCKSKIP=1 KM_HT_NEGTRIED=1 KM_HT_ORD=1` (the 5303
  disjunction-family recipe) + NUMBER+QMERGE+BLOCK=3+incr, the model CONVERGED at
  **8880 nodes (99% blocked) and STOPPED growing** (vs 172898 unbounded without
  those flags). So 15672 is a LIVE ∀+⊔ DISJUNCTION-FAMILY member (⊤-disjunctions
  fire on every node; depth=737955 was BRANCH depth, not node count). Without
  EAGER the matrix (job 47776538) showed identical 132571-node growth across block
  mode 0/2/3, number on/off, nominals on/off — because all of those leave the
  per-node ⊤-disjunction firing intact. **Residual after EAGER+BLOCKSKIP: the
  disjunction SEARCH still times out at 150s** (model bounded, but branching over
  the ~20 unblocked nodes doesn't converge) = the documented hard family problem
  (task #4 convergent disjunction), at a harder scale than 5303. SOUNDNESS of
  EAGER/BLOCKSKIP with number+nominal is UNVERIFIED (they're proven for anywhere-
  blocked ALC(H) no-inverse); must gold-validate if pursued.
  **REFINED (jobs 47777178/47777299): with the full SOUND arsenal
  (EAGER+BLOCKSKIP+NEGTRIED+ORD=1+WATCH+PICK=1 + NUMBER+QMERGE+BLOCK=3+incr) the
  GLOBAL ⊤-consistency CLOSES (rc=0, consistent:true) — model+search converge. But
  the full per-concept classify (82 queries) TIMES OUT at 400s, and KM_HT_PAR=8
  ALSO times out at 250s (peak 505MB). PAR not helping ⇒ NOT throughput: a FEW
  per-concept consistency tests (specific seeds) don't converge = the per-test
  disjunction-family search problem (same as 5303, harder scale). So 15672's
  residual is task #4 convergent-disjunction PER-TEST search, not blocking/
  termination/throughput.** Konclude-time needs that algorithmic work (multi-
  session); the model-folding (EAGER+BLOCKSKIP) is now in hand.
  FINAL (job 47778292): 15672 full arsenal + KM_HT_PAR=16 TIMES OUT at 1800s (30
  min), peak 2.1GB (NOT memory-bound = pure search). So NOT "sound+complete but
  slow" — at least one per-concept test genuinely does not converge at 30x the
  Konclude budget; needs the convergence ALGORITHM (task #4), not tuning. Net
  session-5 verdict: NO current KM engine classifies ANY of 10908/15672/10621
  within even 30x budget (10908: CB global saturation >20min + forced-HT unsound;
  15672: search non-convergent @30min; all inverse-bound). Same-session solve
  impossible without unsound hacks (refused, soundness mandate). Path = fast sound
  inverse-aware engine + disjunction convergence (multi-session).
  CONTESTED-GOLD RULED OUT (pre-computed HermiT sigs km-incr/bigsweep/hermit/):
  10908 HermiT==Konclude EXACTLY (both consistent, 6001 subs, 0 diff) → 593 IS
  satisfiable, KM-HT false-UNSAT is a GENUINE unsoundness bug. 15672 HermiT==
  Konclude (142 subs) → gold correct, KM non-convergence real. 10621 no HermiT sig
  (HermiT errored/timed out too). Both sound reasoners confirm gold; no contested
  escape. HermiT runnable on IBEX: cp /ibex/scratch/hohndor/km/bench/hermit_cp/ +
  module load java; sigs at km-incr/bigsweep/{hermit,konclude}/.
  FULL DERIVATION of 593's false clash (job 47778770, KM_HT_EXPTRACE gated
  add_concept/add_edge logging, added then REVERTED): node1=Q_50 (-3,+9) from its
  filler; node1 ->r1-> node6; role-hier/inverse gives located-in(6,1) (adde r40
  6->1); range/∀ adds concept 108 to node1; 108 forces a REFLEXIVE located-in
  SELF-LOOP (adde r40 1->1, cf cid102 `Q_15->located-in(x,x)`); domain(located-in)
  cid1513 forces +spatial(+3) -> +3∧-3 CLASH. = systemic INVERSE + role-chain +
  REFLEXIVITY over-derivation, deterministically forced (depth-0) where HermiT
  finds a model avoiding it. NOT a one-line fix; likely a disjunct/choice that
  should branch is collapsed deterministically under inverse. Ties 10908 to the
  SAME inverse+disjunction frontier as 15672.
  [Superseded the earlier "infinite ∃-expansion / blocking bug" reading: blocking
  was always correct (i3==full, distinct_triples≈72); the growth was disjunction
  branching, not unfolded ∃.]
- **The paradox (job 47776830, KM_HT_CHAINDUMP added then reverted):** the model
  has only **distinct_cores=23, distinct_triples≈72** — FLAT while nn explodes
  11583→172898. Full `compute_blocked` correctly marks **98-99.96% blocked**
  (~72 unblocked = one per distinct triple). KM_HT_INCRBLOCK2_CHECK (job 47776878)
  shows **i3 incremental == full compute_blocked (NO mismatch panic)** — blocking
  is provably correct. YET expansion keeps creating nodes: a ~72-node unblocked
  frontier that should be the fixed lowest-id representative of each triple (→
  finite model) instead behaves as a MOVING frontier. Mechanism NOT yet pinned:
  by static analysis the incroblig path (oblig_sat + has_rsucc + gather-unblocked-
  only) SHOULD make it finite, so there is a subtle expansion-loop bug specific to
  this ont (note `pending≈nodes`: every node gets a ground ⊤-disjunction — the
  disjunction machinery may be entangled). NEEDS interactive per-pass profiling
  (which nodes expand each pass + their blocked status AT expansion time), not
  remote batch. The fast Ht was NEVER validated on these onts (not ht_routable).
- **10908 root cause = FALSE UNSAT (unsoundness), session 5 late (job 47777528):**
  forcing the fast Ht on 10908 with NUMBER+QMERGE+BLOCK3 declares satisfiable
  concepts UNSATISFIABLE — queries=[593,368,224,223,362] (all SAT per gold) ALL
  come back `unsatisfiable` (in a consistent ont). So consistent([pos(A)]) returns
  FALSE for many A → those concepts emit no real subsumptions → the 5918 "missing"
  (the solve_shoq2 diff only compared SUBSUMPTIONS, not the unsat set, so a false-
  unsat reads as missing not unsound). The MINIMAL Horn chain A->M->B works
  correctly in both plain and NUMBER+QMERGE configs (job 47777492:
  [[A,M],[A,B],[M,B]]) — so it is NOT a basic Horn/propagation bug; it's a SPURIOUS
  CLASH from the number+nominal machinery on 10908's full clause set. ATOM JSON
  KEYS: concept="c" (fields neg,c,t), exists="e", eq="eq", role/edge variants —
  NOT "concept"/"exists" (my first clausetrace mis-parsed and found nothing). The
  593<=224 chain is plain Horn: 593->368->224. Isolation (job 47777544): 593
  false-UNSAT in ALL configs (number on/off, nominals on/off, block 0/2/3) → BASE
  forced fast-Ht, not number/nominal/blocking.
  **EXACT ROOT CAUSE (jobs 47777650/671/697): depth-0 deterministic clash on an
  ∃-successor from RANGE + DISJOINTNESS on a definer node:** cid=1513
  `r40(s,t)->+BFO_0000006(t)` (r40=BFO_0000123, i.e. range(BFO_0000123)⊑BFO_0000006)
  forces +3 on node 1 (a BFO_0000123-target); cid=180 `Q_50->-BFO_0000006` (Q_50
  disjoint BFO_0000006) forces -3 since node 1 carries Q_50 (id 9) ⇒ +3∧-3 clash
  (also cid263 `Q_82∧r19->-3`, cid267 `Q_84∧r37->-3`, cid1108 `Q_135->-3`). Node 1
  is forced to be BOTH Q_50 AND a BFO_0000123-target. `Q_` = FRONTEND DEFINERS for
  nested class exprs ⇒ 10908 false-UNSAT is a CLAUSIFICATION/PROPAGATION interaction
  (definer successor wrongly co-occurring Q_50 + the BFO_0000123 edge), NOT a
  completeness gap. Likely cb_to_ht (definer/range/role-hierarchy) or Ht ∀/range
  too eager. Cross-check: run CB engine on same content → expect 593 SAT. TINs at
  qofull/probe3/{tin_10908.json,fu_full.json,fu_nonom.json}. Diagnostics
  KM_HT_CLASHTRACE (DISJCLASH/CLASHCLAUSE in standalone apply_head ~1213/1324) +
  prop-clash clash-node dump were added then REVERTED (tree clean at 38cf4c9).
  [OLD reading "core test wrongly finds A⊓¬B SAT / entailment-completeness gap"
  SUPERSEDED: it's the opposite — false UNSAT, an unsoundness bug, likely tractable.]
  trace (job 47776562): for missing 593⊑224, the unconstrained model of 593 has a
  NOMINAL-RICH successor node carrying BOTH 593 and 224, but 224 is never FORCED
  onto the root → A⊓¬224 stays satisfiable. A genuine SHOQ entailment-completeness
  gap (nominal/number-driven subsumption not propagating to the root) — the
  calculus piece, separate from termination.
- **Unsound caches confirmed:** KM_HT_SATFOLD / KM_HT_WITREUSE are unsound with
  nominals (label-determined-SAT assumption fails) — do NOT use on nominal onts.
- **CONCLUSION:** the 3 SHOQ targets need (a) a fast Ht that TERMINATES on their
  ∃-structure (the expansion-loop bug) and (b) complete nominal/number entailment
  to the root. Both are substantial; the nominal o-rule alone (below) is necessary
  infra but not sufficient. Stack bumped 1→4 GiB in run_json (lazy, harmless) for
  the deep-recursion path. Chaindump diagnostic was added+reverted.

**NOMINAL O-RULE PORTED INTO FAST Ht (session 5, building):** Ext gains
`nominals: HashSet<C>` + `nom_carriers: HashMap<C,Vec<Node>>`; add_concept records a
fresh positive nominal concept as a carrier (Trail::NomCarrier, LIFO-popped on
backtrack); `process_nominals` (deterministic, called in dfs after propagate, before
obligations) merges all distinct resolved carriers of each nominal into the lowest-id
survivor via the existing dep-tracked `merge_into` (merge dep = union of both
memberships, so a clash backjumps correctly). Ht gains `nom_set` + `set_nominals`,
re-applied to ext each consistent() rebuild. run_json: forced path calls
ht.set_nominals(inp.nominals); KM_HT_NOMINALS env routes nominal(non-inverse) onts to
fast Ht. 2 unit tests (merge→clash unsat, merge→sat). Test config = KM_HT_FORCE +
KM_HT_NUMBER + KM_HT_QMERGE + KM_HT_BLOCK=3 + incr flags. 10621 flags pending (28MB
dump slow).

**DECISIVE WHOLE-FAMILY CHARACTERIZATION (session 4, 8 IBEX experiments) — every
member profiled; the 9 split but share ONE root blocker = fast sound INVERSE
[SUPERSEDED for 10908/15672 by the session-5 correction above]:**
- **3215** (ONLY no-inverse non-nominal member; SHI, 54973 q, branch_pushes=0
  everywhere = NON-branching/Horn): per-concept models are HUGE (concept 95 = 2785
  nodes / 41s, prop_ms dominates) from transitive `__trans__` ∀-propagation; node
  cores are CONTEXT-SPECIFIC (position in role chain) so they DON'T recur → ALL
  cross-concept caches inert: satfold hits=0 (needs a branch point, 3215 never
  branches), witreuse ~0, and **my satcache3 (KM_HT_SATCACHE3, mode-3 cross-model
  core-keyed blocking, built+CHECK-validated+suite-133/0 but REVERTED) measured
  INERT — 3215 still TIMES OUT (concept 73=2381 nodes/35s with it on)**. 3215's
  wall = transitive ∀ propagation VOLUME, not caching/branching/blocking-speed.
  Needs deep transitive-propagation/fold work (NOT a bounded session piece).
- **7914/9663/14817** (SRIQ): qmerge makes them COMPLETE now, but inverse + large
  → per-concept speed wall (timeout).
- **9724** (Horn-SHIF functional, 23136 q): 2.5M inverse reversed edges → inverse-
  bound, ∀-pollution in QoSat.
- **10908(SROIQ)/10621(SOIF)/15672(SHOIN)**: nominal + INVERSE = SHOI/SHOIQ, which
  cb_to_ht.rs:552 FENCES (drops nominals). Nominals ARE implemented in LEGACY
  Tableau (tableau.rs apply_nominal_merges, sound SHOQ no-inverse) but it hangs on
  real onts; fast Ht has none. Basic nominal-merge port to Ht = SHOQ only, does
  NOT cover these (they're nominal+inverse).
- **CONCLUSION:** all 9 are INVERSE-bound (inverse+count / inverse+cardinality /
  inverse+nominals) — exactly where fast Ht is unsound/unsupported and sound paths
  (CB/legacy-tableau/per-concept Ht) are too slow/OOM. The unifying missing piece
  is ONE large unit: a fast SOUND inverse-aware saturation-caching SHIQ/SROIQ
  completion engine (the project_km_shiq_ht Phase-3 work). No bounded port flips an
  inverse-bound member. satfold/witreuse/satcache (incl. satcache3) are all sound
  ONLY for no-inverse core-determined SAT, so they help at most 3215 — and even
  there they're inert (transitive volume). findqc CAND small n≥2-qual onts (no-inv,
  no-nom) for qmerge gold tests: 10019/12653(timeout, base HT too slow)/16461(MATCH)/
  11296.

**LANDED earlier (commits 090a273…6acac27, payg-strategy):**
- KM_HT_QO_INVCHAIN (compose virtual inverse in chain bodies), KM_HT_QO_RESIDUE
  (model-reuse residue), tunable branch limits, taint-defer, KM_HT_QO_DUMP_AFFECTED.
- **P2.1 (6acac27, gated KM_HT_QO_SHIQ, 131 tests pass):** non-shared per-source
  successors in the Exists rule (parent link `qo_parent`, maintained in
  new_node/rollback; fixes latent is_filler rollback leak) + suppress critical-ALL ∀
  insufficiency under shiq (sound now) + `qo_blocked` B1 ancestor subset blocking.

**MEASURED (isolated `km tableau` on dumped TInputs; how-to below) — the crux:**
- Shared sound-∀ pass (P2.1, all concepts at once): 7914 → **27GB (no block) / 31GB
  OOM (B1 block)**. Blocking caps tree DEPTH not BREADTH; one in-memory pass holding
  all 17680 roots' non-shared trees is inherently ×concepts memory.
- Per-concept `Ht::consistent` (one at a time, block_mode=3 + KM_HT_NUMBER + all
  caches satcache/lblcache/satfold/witreuse, PAR=1): memory FINE (490MB) but 1000 of
  7914's 7171 affected TIME OUT at 150s. block_mode=3 (sound for inverse) is NOT
  incremental (incr2 only mode 1 → blocking recompute dominates) + explosive
  disjunction concepts.
- Earlier: complete HT on ALL concepts (block_mode=1, PAR=8) also timed out; QO-force
  is unsound (7914: 190539 vs gold 141517 from shared-filler ∀ pollution).

**Conclusion = the remaining pieces (all substantial, next sessions):**
1. **Incremental pairwise (mode-3) blocking** — extend the incr2 incremental-blocking
   path (currently mode-1 only, hypertableau.rs:4953) to block_mode 3, so the sound
   per-concept completion is fast. THIS is likely the highest-leverage single piece.
2. **Content-addressed saturation cache** (Konclude tryEstablishSaturationCaching):
   cache a node's saturated label + blocking status by its initial forced-concept
   set, reuse across the per-concept completions. KM's witreuse/satcache are partial.
3. **n≥2 qualified ≤-merge + choose-rule** (apply_head:1025 gap) for the cardinality
   onts (9724 number=true).
4. **Disjunction convergence** (planORProcessing delaying + dependency backtrack +
   nogood) for the explosive concepts (7499/3215/7914 tail).
Per-concept (memory-bounded) + (1)+(2) is the viable path; the shared single pass is
NOT (×concepts memory). NONE of the 9 solved yet.

**DECISIVE SCALE FINDING (600s correctness run):** correctly-configured SOUND
complete-HT (block_mode=3 + KM_HT_NUMBER + satcache+lblcache+satfold+witreuse + incr
+ PAR=8) at a 600s budget (4× target) → 9724 TIMEOUT 600s, 7914 TIMEOUT 600s (both
no sig). So the gap is ORDERS OF MAGNITUDE, not constant-factor: incremental mode-3
blocking + existing caches will NOT bring the sound per-concept path within even 4×
budget. Reaching Konclude's <150s needs Konclude's full saturation-caching
completion (subtree-level cached saturations + saturation-blocking prediction +
disjunction delaying) ≈ reimplementing its completion engine = multi-month. P2.1 is
the right foundation; the speed core (P2.2-P2.4 to Konclude standard) is the bulk
and is large. This is the realistic scope for the next sessions.

**SESSION 6 (2026-06-25) re-grounding + satcache3 redux:**
- **Baseline job 47780523 (P2.1 KM_HT_QO_SHIQ shared pass):** 10908 km_cons=TRUE now
  (P2.1 sound-∀ FIXED the false-UNSAT — was inconsistent, now consistent, only 3
  spurious) BUT reads only **86/6001 subs (missing 5918)** — the shared pass isolates
  each concept's tree so cross-concept subsumption is lost; 15672 no GOLD line
  (timeout). CONFIRMS design-doc: shared-pass = dead end (sound-ish ∀ but
  reading-incomplete + OOM/timeout at scale). Tasks #7/#8/#10 (shared pass) closed.
- **satcache3 REDUX (this session):** re-implemented KM_HT_SATCACHE3 but with
  FULL-LABEL i3 signatures (pos+neg core(n)+core(pred)+edge-roles) instead of the
  prior REVERTED core-keyed version — full-label is SOUND cross-query (carries this
  query's negatives so a pooled block can't skip a forbidden-concept clash; core-key
  was unsound). Pools unblocked clash-free mode-3 nodes after SAT; consume in
  compute_blocked mode-3 (forces off incr path when on). Built clean on IBEX
  (BUILD_RC=0). Validation job 47780623 (sc3v.sbatch): cargo test + i3==full CHECK +
  3215 off/on + 15672/7914/9724 @600s vs gold + branch/pool stats. NOTE prior memory
  verdict (lines ~244-266): caches help AT MOST 3215 and even there INERT (3215 wall
  = transitive-∀ VOLUME, never branches, context-specific cores don't recur); the
  throughput targets are INVERSE-bound where mode-3 itself is unsound (10908
  false-UNSAT). So full-label satcache3 is the SOUND variant the prior never validly
  tested on 7914/9724 — job 47780623 closes that open question. Code UNCOMMITTED
  pending numbers (don't commit a known-inert path unless 7914/9724 prove otherwise).
- **REAL next engine piece (per all evidence):** sound INVERSE-aware reasoning = real
  inverse EDGES + DOUBLE-BLOCKING (SHIQ), replacing the bridging-clause inverse that
  over-derives (10908: bridging cid1304 makes node1 a located-in SOURCE → reflexive
  self-loop → domain forces +spatial → false clash). Mode-3 pairwise is sound only
  for SH WITHOUT inverse; the targets need the stronger double-blocking. THIS is the
  foundation the saturation cache must sit on — more fundamental than the cache.

**SESSION 6b LANDED (2026-06-25, commit 99a21d1, payg-strategy) — SHIQ double-blocking
(block_mode 4) + indirect blocking, gated + synthetic-tested, build+tests on ws:**
- **block_mode 4 (KM_HT_BLOCK=4):** SHIQ double-blocking (Horrocks/Sattler/Tobies).
  Block n by the first earlier unblocked node with identical `i3_signature_full(n,p)`
  = FULL label(n) (pos AND neg, `(c<<1)|neg`) + FULL label(pred n) + the pred↔node
  edge roles in BOTH directions (forward `r<<1` from in_edges, backward `(r<<1)|1`
  from out_edges). Mode-3's positive-core key is sound only WITHOUT inverse; mode-4
  matches negatives + the inverse edge so unraveling the blocker respects every
  constraint. Mode-4 always uses the full `compute_blocked` (process_obligations incr2
  guard excludes it).
- **INDIRECT BLOCKING (the piece that makes it TERMINATE):** a backward universal
  (∀r⁻.C) completes a node's label only AFTER its successor exists, so the frontier
  node never *directly* matches an earlier complete node → infinite chain (this was a
  real HANG, caught by the synthetic test `mode4_inverse_model_is_satisfiable`). Fix:
  a node with a (directly/indirectly) blocked PREDECESSOR is itself blocked and must
  not be expanded. One ascending pass (`pred[n] < n`) after the direct-block loop in
  the mode-4 branch propagates transitively. SOUND (gates only ∃-expansion, never the
  clash raise in add_concept) + COMPLETE (HST). Without it the simple inverse cycle
  (A⊑∃R0.A, immediately-complete labels) terminates but ∀-over-inverse does not.
- **KM_HT_SATCACHE3 (default off):** full-label cross-query saturation cache consumed
  in the mode-3/4 blocking path; sound full-label variant (carries the query's
  negatives), inert until opted in.
- **6 synthetic unit tests** (all pass; FULL lib suite 141/0): inverse-cycle
  termination, backward-inverse-propagation clash + its satisfiable twin (the
  indirect-blocking regression test), no-inverse regression, merge×inverse×double-block
  cycle SAT + clash UNSAT. merge_into already carries in+out edges so cardinality
  under inverse flows through the same Eq-head path.
- **GOTCHAS this session:** (1) BUILD/TEST UNIT TESTS ON ws, NOT the IBEX login node
  ([[feedback_build_before_benchmark]]). (2) rsync -a preserves laptop mtime → cargo
  skips recompile (stale binary ran old 141 tests, "0.03s Finished" + "N filtered
  out" = tell); always `touch src/*.rs` after rsync before building. (3) `cargo test
  <name> -- --exact` needs the FULL module path `tableau::hypertableau::tests::<name>`;
  use a bare substring filter (no --exact) instead — "N filtered out / 0 passed" = the
  filter matched nothing. (4) two concurrent `cargo test` deadlock on .cargo-lock
  (procs alive, no progress, empty output) — kill stragglers by PID, run ONE.
- **NEXT:** mode-4 is the inverse foundation; still to build = wire mode-4 into the
  inverse-routing path (replace/augment bridging-clause inverse), the saturation cache
  on top, and convergent disjunction (task #4). Then ONE full ORE sweep.

**SESSION 6c LANDED (2026-06-25, commit a853e1e) — PORTED Konclude optimized blocking
(KM_HT_BLOCK=5), per user HARD RULE [[feedback_port_from_konclude]] (port, don't
invent):** from `CCalculationTableauCompletionTaskHandleAlgorithm.cpp::isLabelConcept
OptimizedBlocking`. Full faithful spec extracted to **docs/KONCLUDE-BLOCKING-SPEC.md**
(B1/B2a/B2b/B3-B6 + dispatcher + indirect, line-referenced).
- **B1 = L(w) ⊆ L(w') SUBSET** (NOT equality). KEY INSIGHT: subset directly folds the
  ∀-over-inverse frontier-lag that hung textbook pairwise mode-4 — an incomplete
  frontier {B} ⊆ complete blocker {B,CC} blocks immediately, no need to wait for its
  successor to complete its label. (So mode-5 is strictly better than my mode-4 here;
  mode-4 needed the indirect-block workaround, mode-5 terminates via subset alone.)
- **B2a = soundness-under-inverse**: for each role r on a w→v edge (v=pred(w), the
  inverse direction the bridging clauses materialise), every ∀r.D the blocker w'
  carries must already hold at v. KM has NO explicit ∀r.C concepts — ∀ is the clause
  `C0(x)∧r(x,y)→D(y)`; new `index_forall` keys these by (C0,r)→D, built once at
  Ht::new; `b2a_holds(w,wp,v)` consults it. Plain subset is UNSOUND under inverse;
  B2a is exactly what restores soundness.
- Indirect-block pass reused. DEFERRED (in spec): B2b automata/transitive ∀; B3-B6
  at-most/at-least cardinality (c-/a-blocked).
- 5 synthetic tests (mode-5 reproduces mode-4's sound verdicts incl. frontier-lag SAT
  via subset+B2a; index_forall unit). FULL suite 146/0 on ws. Gated KM_HT_BLOCK=5,
  default 1 unchanged.
- HONESTY: deferred a dedicated "B2a REFUSES to block" discriminator test (hard to
  hand-craft a confidently-predictable case); inverse_model SAT proves B2a PERMITS
  sound blocking. Add the refusal discriminator later.
- **Konclude source IS ON LAPTOP** at Public/software/Konclude/Source/Reasoner/Kernel/
  Algorithm/ — reading is laptop-safe. Use it to port the remaining pieces.
- **NEXT (all Konclude ports):** B2b + cardinality B3-B6 into mode-5; wire mode-5 as
  the auto-selected blocking for inverse onts (route, don't env-flag); then saturation
  caching (tryEstablishSaturationCaching) + disjunction delaying (planORProcessing).

**SESSION 6d LANDED (2026-06-25, commit 257188b) — auto-route inverse→mode-5 + B2b
finding:** `has_inverse_bridge(clauses)` detects inverse structurally (bridging clause
`s(a,b)→r(b,a)`, swapped vars, distinct roles — the `inverse` flag is unreliable),
mirrors compose_inverse's bridge_of. Ht::new auto-selects mode 5 when inverse present
(port of Konclude default optimized-blocking), GATED KM_HT_AUTOBLOCK (default off,
explicit KM_HT_BLOCK/SUBSET_BLOCK wins). 1 unit test, suite 147/0 on ws.
**KEY FINDING — B2b is PRE-COMPILED in KM:** Konclude's runtime ∀-automata/transitive
B2b is mostly subsumed because KM's frontend (preprocess.rs::transitivity_clauses)
compiles transitive-role ∀ into `__trans__R__C` concept-propagation clauses at PARSE
time (`R∧⋀Ci(y)→P(x)`, `R∧P(y)→P(x)`, `Γ∧P(x)→Δ`), so the transitive consequences are
ORDINARY label concepts that B1 subset already covers. Konclude keeps ∀-automata at
runtime; KM moved that to parse time. **Cardinality B3-B6 ≠ direct port:** KM has no
≤n/≥n label operators — ≤n is Eq-head merge, ≥n is distinct-succ + distinctness
clauses; cardinality-under-blocking soundness rests on merge+distinctness+B1. Both
findings = CONFIRM on transitive/number ORE onts at validation, port the specific
check only if a gap appears. So mode-5 (B1+B2a+autoroute) is a coherent sound
milestone for the inverse fragment, NOT a soundness shortcut. docs/KONCLUDE-BLOCKING-SPEC.md
updated with both findings.
**NEXT:** the productive ORE-validation wiring (race.rs: route real inverse onts to
mode-5 via KM_HT_AUTOBLOCK) — deferred to engine-complete per build-first rule; then
saturation caching + disjunction delaying (the remaining big Konclude ports).

**How to iterate (IBEX):** build `cd /ibex/scratch/hohndor/km/engine && touch src/*.rs
&& cargo build --release` (~75s). Dump a TInput once:
`KM_DUMP_TIN=tin.json km classify <ont>`; then isolate the engine with
`km tableau < tin.json` under `KM_HT=1 KM_HT_FORCE=1 ...` (KM_HT=1 REQUIRED or it runs
legacy tableau). Restrict queries to affected: python-edit tin.json `queries` to the
KM_HT_QO_DUMP_AFFECTED ids. Gold sigs at /ibex/scratch/hohndor/km/gold/. Run on
compute nodes via sbatch (account pi-hohndor, partition batch), never the login node.
Corpus /ibex/scratch/hohndor/km/corpus/. See also [[project_km_shiq_ht]],
[[project_km_flag_sweep]], [[project_km_konclude_study]].

**SESSION 6e (2026-06-25, commit 1866dda) — disjunction-processing port SPEC ready
(docs/KONCLUDE-DISJUNCTION-SPEC.md); implementation = next work cycle.** Extracted
faithfully from Konclude planORProcessing/executeORBranching/backtrackFromTrackingLine/
writeClashDescriptorsToCache. KM ALREADY HAS PendingDisj, eval_disj (unit-prop), dep-set
backjump, KM_HT_LEARN (INERT), KM_HT_EAGER (defer to unblocked nodes). GAP to port (3,
gated+synthetic-tested):
  1. **Trigger-based DELAY** (planORProcessing 16489) = highest-leverage convergence
     lever for 15672 + disjunction family. Konclude defers a disjunction until a TRIGGER
     concept/role appears (searchNextConceptRoleBranchTrigger 17217); KM only defers to
     UNBLOCKED nodes, not per-disjunction relevance. Map via concept_triggers/role_triggers;
     gate KM_HT_ORDELAY.
  2. **Semantic branching** (executeORBranching 16737, mConfAtomicSemanticBranching): add
     atomic negated operands of other disjuncts (KM_HT_NEGTRIED nearest).
  3. **Sound nogood cache** (writeClashDescriptorsToCache 7400): redo KM_HT_LEARN with
     Konclude restrictions — single node, NO nominal, NO propagation concept, non-atomic,
     canonicalized; 3-phase backtrack filters by PROCESSING TAG (7126) so only post-choice
     clashes learned.
Touches certified calculus core → Lean re-cert at END; argue derived set unchanged
(delay/cache = search-order + redundancy, fixpoint-preserving; semantic branching adds
sound negations). Blocking spec: docs/KONCLUDE-BLOCKING-SPEC.md.

**SESSION 6f FINDING (2026-06-25) — KM ALREADY HAS the disjunction pieces; do NOT
re-port them.** Reading KM's dfs against the disjunction spec: (1) trigger-DELAY ≈
present — dfs (hypertableau.rs:6044) saturates ALL deterministic rules (propagate +
process_nominals + process_obligations) to a full fixpoint via `if _made {continue}`
BEFORE branching any disjunction (next_action_incremental:6079); plus KM_HT_TRIGABS
absorbs ⊤-disjunctions into triggered clauses. (2) semantic branching ≈ KM_HT_NEGTRIED
(branch loop ~6189): on a disjunct clash, asserts ¬D_i (dep = clash∖level) so siblings
unit-propagate. (3) sound nogood cache ≈ KM_HT_LBLCACHE/lblng (~6149): SIGNATURE-keyed
no-goods independent of node-ids (the fix for the broken node-uid KM_HT_LEARN). So the
3 disjunction pieces are faithfully present already, and prior IBEX diagnostics
([[project_km_ht_learning_dead]], project_km_ht_search) showed these levers (in KM's
form) do NOT crack the disjunction family (15672 non-convergent @30x even with the full
arsenal). ⇒ The genuine remaining Konclude differentiator is ARCHITECTURAL: LAZINESS via
SATURATION CACHING ([[project_km_konclude_study]] P1/P2) — Konclude decides ~95% of
concepts by cheap incomplete saturation + caches, full tableau only on residue; KM runs
the COMPLETE tableau everywhere. PIVOTED the port effort to tryEstablishSaturationCaching
(~21670) + tryEstablishExpansionBlockingWithBackendCacheSynchronisation (~22582) — task
#3. Extraction agent launched 2026-06-25; spec → docs (next). NB 10908's blocker was
inverse-soundness (mode-5 a853e1e addresses it), NOT disjunction; 15672 is the
disjunction-family/laziness case.

**SESSION 6g DECISIVE FINDING (2026-06-25) — the content-addressed saturation cache is
ARCHITECTURALLY INERT in KM; do NOT implement it.** Full Konclude saturation-cache spec
extracted (docs/KONCLUDE-SATURATION-CACHE-SPEC.md, committed 454b19c). On reading KM to
port it: KM ALREADY HAS the content-addressed cross-concept reuse = the global forward
QoSat pass — `ensure_filler` in sat_mode (hypertableau.rs:3188) keys successor nodes by
`(filler-concept, role)` in `sat_filler`, ONE saturation node shared across ALL concepts
in a single pass; qo_classify_global_fwd (7176) reads each concept's subsumers off its
self-node with Konclude's exact 3-state (clean→SAT, node_unsat→UNSAT, affected→defer).
The residue verify funnel (KM_HT_QO_VERIFY, 7396) then runs `qpc.saturate(&[pos(a)])`
**once per suspect concept** (line 7534) — each (concept,neg) saturated EXACTLY ONCE per
classification ⇒ a (concept,neg) cache has ZERO within-classification hits (confirms the
prior satcache3 inert result + project_km_family_diagnosis "~1% hit"). So the cache the
user asked to port provides ~no benefit in KM's architecture. This is the THIRD major
Konclude mechanism found ALREADY PRESENT this session (after disjunction heuristics and
the saturation gate). **CONCLUSION: the path to the targets is NOT porting more
mechanisms — they exist. It is (1) the mode-5 blocking port (a853e1e, genuinely NEW
fidelity, SOUND under inverse, targets 10908's known false-UNSAT) — VALIDATE on 10908;
(2) wiring/integrating the existing pieces. Re-porting existing mechanisms = duplication;
refused (integrity).** Recommend: targeted IBEX-compute validation of mode-5
(KM_HT_AUTOBLOCK) on 10908 vs gold — soundness signal, not timeout-noise.

**SESSION 6h VALIDATION RESULT (2026-06-25, IBEX job 47782403, batch cn604-09) —
mode-5 does NOT fix 10908; the bug is inverse PROPAGATION, not blocking. DECISIVE.**
A/B forced-Ht (KM_HT_FORCE+NUMBER+QMERGE+NOMINALS) on 10908, block=3 vs block=5, vs
gold (6001 subs / 1 unsat):
  - block=3: 86 subs, 664 unsat, MISSING=5918, EXTRA=3, consistent=true.
  - block=5: **BYTE-IDENTICAL** (same sig_sha 7d73a7cc…) — 86 subs, 664 unsat,
    MISSING=5918, EXTRA=3. mode-5 changed NOTHING.
WHY: 10908's false-UNSAT (664 unsat vs gold 1) is a DETERMINISTIC depth-0 clash from
the bridging-clause inverse over-derivation (cid1304 inverse bridge → reflexive
located-in self-loop → domain cid1513 forces +spatial → +3∧¬3 clash), which fires in
deterministic propagation BEFORE any blocking decision. Blocking mode is irrelevant to
a depth-0 clash by construction. So mode-5 (sound, synthetic-validated, commits
99a21d1/a853e1e/257188b) is correct FOUNDATION for inverse blocking but is NOT the
10908 fix. **The actual 10908 fix = sound inverse EDGE/PROPAGATION handling that does
not force node1 to be a located-in SOURCE via the reflexive self-loop** (the "real
inverse edges" half of task #11, replacing/correcting the bridging-clause inverse
over-derivation). NEXT: trace the exact over-derivation (KM_HT_EXPTRACE / the cid1304→
cid1513 chain) and fix the inverse-edge semantics so the spurious located-in(x,x)
self-loop / +spatial is not deterministically forced. Keep mode-5 (sound, useful for
inverse onts WITHOUT this bridging bug). 10908 build on IBEX compute = 48s; run = 1.4s
/ 13MB (fast, confirming it's a soundness bug not throughput).

**SESSION 6i 10908 ROOT-CAUSE PINNED (2026-06-25) — ObjectHasSelf + inverse + domain.**
Per user directive (trace Konclude FIRST, then route KM the same way). 10908 OWL has
`SubClassOf(BFO_0000006 ObjectHasSelf(BFO_0000083))` and `ObjectHasSelf(BFO_0000123)`
(spatial ⊑ ∃located-in.Self; 6 HasSelf, 0 ReflexiveObjectProperty, 24 inverse, 11
DisjointClasses). Konclude CONFIRMS BFO_0000015/0000020/0000004 all SATISFIABLE in ~1ms
(consistency=gold); KM forces 664 false-unsat. EXACT KM clauses (tin_10908.json dumped via
KM_DUMP_TIN; NB KM_DUMP_TIN then runs FULL classify → CB engine TIMES OUT, kill the job,
the TIN is already written): r1=BFO_0000083, r40=BFO_0000123 (inverse pair via cid1303
`r40(a,b)→r1(b,a)` + cid1304 `r1(a,b)→r40(b,a)`); c3=BFO_0000006(spatial), c108=Q_15
(ObjectHasSelf(r40) definer), c9=Q_50.
  - cid102 `Q_15→r40(x,x)`, cid103 `r40(x,x)→Q_15`, cid104 `spatial→Q_15` (the Self iff).
  - cid1513 `r40(x,y)→spatial(x)` = DOMAIN(BFO_0000123)⊑spatial; cid1491 `r1(x,y)→spatial(y)`
    = RANGE(BFO_0000083)⊑spatial; cid1514 `r40(x,y)→c19(y)` = range(r40)⊑c19.
  - cid180 `Q_50→¬spatial`; cid179 `Q_50→c19`.
MECHANISM: a node carrying Q_50 (¬spatial) gets forced into a BFO_0000123 (r40) self-loop
(→ domain cid1513 → +spatial → +3∧¬3 clash). Self-loop entry point NOT yet pinned by
static analysis (Q_15←spatial←r40-self is circular); the inverse bridges (r1↔r40) +
ObjectHasSelf interaction must inject an r40 edge KM shouldn't. NEXT: trace job 47782703
(KM_HT_EDGETRACE added to Ext::add_concept/add_edge, gated; restrict TIN queries=[15], run
`km tableau < tin_15.json` KM_HT=1 KM_HT_FORCE=1 mode-5) → read the AE/AC chain to the CLASH
to find the wrong firing, then fix the inverse+Self+domain interaction to mirror Konclude
(which never forces the self-loop on a ¬spatial node). Konclude bin:
bench/reasoners/Konclude-.../Binaries/Konclude satisfiability -i ont -x IRI (LD_LIBRARY_PATH
=bench/reasoners/libs). EDGETRACE is UNCOMMITTED diagnostic (revert after).

**SESSION 6j — over-derivation CHAIN pinned (2026-06-25, trace job 47782703, KM_HT_EDGETRACE
on BFO_0000015 forced-Ht mode-5, queries=[15], verdict=unsatisfiable=BUG).** The exact
edge/concept sequence to the clash:
  82:  AE r1  n1->n3   (n1 -located-in(BFO_0000083=r1)-> n3; n3 = the spatial filler of
                        BFO_0000004 ⊑ ∃located-in.spatial)
  130: AE r40 n3->n1   (INVERSE BRIDGE cid1304 r1(a,b)→r40(b,a): r1(1,3) ⇒ r40(3,1))
  131: AC n1 +108(Q_15)  ← forced here, RIGHT AFTER the inverse edge
  132: AE r40 n1->n1   (self-loop via cid102 Q_15→r40(x,x))
  134: AC n1 +3(spatial) → clashes with n1's Q_50→¬spatial (cid180) ⇒ false UNSAT.
ROOT CAUSE = KM concludes "located-in a spatial region ⇒ spatial", which is UNSOUND (a
process located-in a region is not itself spatial); Konclude never does this (BFO_0000015
SAT in 1ms). The inverse bridge r40(3,1) + the ObjectHasSelf/∀ interaction force +Q_15/+spatial
onto n1. ONLY cid102/103/104 write c108 (no general range(r40)→108), so +108 on n1 (target of
r40(3,1)) comes from either: (a) cid103 r40(x,x)→108 IF n1/n3 got nominal-MERGED (10908 has 18
nominals) making r40(3,1) a self-loop, or (b) a backward ∀ `C(n3) ∧ r40(n3,n1) → 108(n1)`.
NEXT: pin the culprit clause — add clause-id to the edge/concept trace OR check whether n1,n3
are nominal carriers that wrongly merge. Then mirror Konclude (do not force spatial on the
located-in occupant). The fix is in the inverse/nominal/∀ interaction, NOT blocking. Full edge
list: r4 n0->n1, r0 n0->n2, ..., r1 n1->n3 (82), r0 n1->n4 (84), r40 n3->n3 (114, n3 self-loop),
r40 n3->n1 (130). n3 carries +102..+108 (spatial-ish: it IS the spatial filler).

**SESSION 6k — CULPRIT CLAUSES + likely SPURIOUS MERGE (2026-06-25, trace job 47782788,
cid-tagged FIRE trace).** The clauses forcing the clash on n1:
  - **cid103 `r40(x,x)→Q_15(c108)`** fires +108 on n1 ⇒ n1 ALREADY HAS an r40(1,1) SELF-LOOP.
  - **cid1513 `r40(x,y)→spatial(x)`** (domain BFO_0000123) fires +3(spatial) on n1 ⇒ n1 is an
    r40 SOURCE (the self-loop) ⇒ +spatial ⇒ clash with cid180 Q_50→¬spatial.
KEY DEDUCTION: n1's +Q_15 came from cid103 (needs r40(1,1) present); the OTHER self-loop
producer cid102 (Q_15→r40(x,x)) needs Q_15 first ⇒ CIRCULAR, cannot bootstrap. So n1's
r40(1,1) self-loop can ONLY have arrived via a NODE MERGE: n1 merged with the spatial filler
n3 (n3 has its own r40(3,3) self-loop from spatial→Q_15→cid102), and merge_into rewrote n3's
self-loop onto n1 (r40(3,3)/r40(3,1) → r40(1,1)). That makes n1 spatial ⇒ false clash. Konclude
= BFO_0000015 SAT in 1ms ⇒ the MERGE IS SPURIOUS (a ¬spatial Q_50 node must not merge with the
spatial filler). ⇒ 10908's bug = a SPURIOUS NODE MERGE under the nominal-o-rule (38cf4c9, 18
nominals) OR a ≤1 functional merge (KM_HT_NUMBER+QMERGE), interacting with ObjectHasSelf+inverse
— NOT blocking, NOT the bridging clauses per se. NEXT: log merges (process_nominals / merge_into
/ branch_merge) on the BFO_0000015 trace to see WHICH merge fires and on which (nominal/≤1)
trigger; confirm it's spurious; then prevent it (mirror Konclude — keep the located-in occupant
distinct). Re-run WITHOUT KM_HT_NOMINALS and/or WITHOUT KM_HT_QMERGE to bisect which merge
source causes it (cheap A/B). EDGETRACE+FIRE diag edits UNCOMMITTED on laptop+IBEX (add_concept,
add_edge, apply_head) — revert before any commit.

**SESSION 6l — BISECTION + edge-cid trace ⇒ NOT a flag-merge; likely SHARED-FILLER-NODE
conflation (2026-06-25, jobs 47782807 bisect, 47782820 edge-cid).** Bisection: BFO_0000015
stays false-UNSAT in ALL of {ALL, no-NOMINALS, no-QMERGE, no-NUMBER/QMERGE, no-NUM/QM/NOM} ⇒
the spurious self-loop is NOT a nominal-o-rule / ≤1 / qmerge MERGE. Edge-cid trace: 158 `r1
n1->n3` (located-in); 250 cid1304 `r1(1,3)→r40(3,1)` (inverse bridge); 254 cid102 `Q_15→r40(1,1)`
(self-loop); 256 cid1303 `r40(1,1)→r1(1,1)`. cid102 (Q_15→r40 self) and cid103 (r40 self→Q_15)
are MUTUALLY CIRCULAR and merges are ruled out ⇒ the cycle can only be entered if n1 is
STRUCTURALLY identified with the spatial filler node (KM's SHARED FILLER NODE: one node per
filler concept). So n1 (the ¬spatial Q_50 located-in occupant) is being CONFLATED with the
spatial filler, inheriting its ObjectHasSelf(r40) self-loop → cid1513 domain → +spatial →
clash with cid180 Q_50→¬spatial. Flag-independent (matches bisection). SAME root as the QoSat
shared-filler ∀-pollution. ⇒ **FIX = NON-SHARED successors in the forced-Ht path** (the P2.1 /
task #7 work: sat_mode ensure_filler 3188 keys by (fil,role) = SHARED; needs per-source fresh
successor so the occupant is not identified with the filler). Konclude uses independent
successors (applyALLRule into non-shared nodes) — this is exactly the routing to mirror. NEXT:
VERIFY the hypothesis — check if n1 and n3 are the same/shared node (or that ensure_filler /
the Ht's ∃-expansion shares the spatial filler with the occupant); then route 10908 to the
non-shared-successor path (KM_HT_QO_SHIQ P2.1 already builds non-shared successors — test
BFO_0000015 under it) and confirm SAT. If P2.1 non-shared makes BFO_0000015 SAT, that's the
fix to wire. UNCOMMITTED diag: revert add_concept/add_edge/apply_head EDGETRACE before commit.

**SESSION 6m — BUG FOUND + FIXED: fire_anchor_edge matched a SELF-LOOP body atom against a
NON-SELF edge (2026-06-25).** The chronological single-file trace (t15c.err): 158 `AE r1
n1->n3`; 250 cid1304 `r1(1,3)→r40(3,1)`; **252 cid103 `r40(x,x)→Q_15` FIRES on n1** — i.e. the
self-loop clause cid103 (body `r40(s=0,t=0)` = r40(x,x)) fired on the NON-self edge r40(n3,n1)
(n3≠n1). ROOT CAUSE in `fire_anchor_edge` (hypertableau.rs ~1445): for a body role atom it does
`sigma[sv]=Some(es); sigma[tv]=Some(et);` — when sv==tv (self-loop atom, both vars=0) the second
assignment OVERWRITES the first and the es==et constraint is SILENTLY DROPPED, so r(x,x) wrongly
matches r(es,et) with es≠et, binding x=et. ObjectHasSelf produces these self-loop clauses
(spatial→r(x,x) cid102, r(x,x)→Q_15 cid103); the inverse bridge produces non-self edges r40(n3,n1)
→ cid103 fires → Q_15(n1) → cid102 self-loop → cid1513 domain → +spatial → clash with cid180
Q_50→¬spatial ⇒ 664 false-unsat. FIX (committed-pending): in fire_anchor_edge, `if sv==tv && es!=et
{ return; }` before binding — a self-loop body atom only matches a self edge. SOUND (removes a
spurious derivation), COMPLETE (genuine self edges es==et still match), flag-INDEPENDENT (explains
the bisection: not nominal/number/qmerge). rec_match_flex is CORRECT (sv==tv share one sigma slot
⇒ it checks r(sn,sn)); bug was ONLY the anchor's explicit double-assign. Validation job 47782866:
cargo test no-regress + BFO_0000015 SAT? + full 10908 vs gold (MISSING 5918→?). If it works this is
the 10908 fix (and likely helps the inverse+ObjectHasSelf family). REMEMBER: revert EDGETRACE/FIRE
diag (add_concept/add_edge/apply_head) before committing the fix.

**SESSION 6n VALIDATED — self-loop fix is REAL + PARTIAL; 10908 has THREE layers (2026-06-25).**
Fix in TWO sites (DIAG REVERTED, fix kept, 147/0 ws): fire_anchor_edge ~1445 `if sv==tv && es!=et
{return}` (Ht path) + fire_role_clause ~4151 `if *s==*t && es!=et {continue}` (QoSat path). Per-
concept `km tableau` results (queries=[id], fresh binary, forced mode-5): id7/15/19/23 = SAT
(were UNSAT — FIX WORKS); id11(BFO_0000020) = UNSAT even ALONE (residual, fix doesn't cover);
FULL 692-query batch = 664 unsat (BFO_0000015 SAT-alone becomes UNSAT in batch ⇒ shared-filler
CROSS-QUERY contamination). So 10908 = THREE issues: (A) self-loop-match bug [FIXED, commit];
(B) a residual per-concept over-derivation (BFO_0000020) [investigate next, same trace method];
(C) shared global-pass filler pollution [P2.1/task#7, route to per-concept/non-shared]. The
self-loop fix is sound + no-regress + genuinely flips several concepts SAT ⇒ COMMIT it as real
correctness progress even though 10908 not fully solved. ore_runone forces OLD engine binary
(KM_ENGINE=bench/km/kobayashi-marust-par); to test fresh binary use `km tableau < tin.json`
directly. NEXT: trace BFO_0000020 (id11) alone for residual (B); then non-shared routing for (C).

**SESSION 6o — layer B (BFO_0000020 residual) clash site HUNT (2026-06-25, jobs 47782976/985/991/997).**
Self-loop fix COMMITTED (592cf27, clean). Hunting BFO_0000020's residual false-UNSAT: added gated
KM_HT_EDGETRACE markers at SIX clash sites and re-ran id=11 each time — ALL EMPTY, yet verdict =
unsatisfiable[BFO_0000020]: (1) Ht add_concept complement (ET CLASH); (2) Ht free-fn apply_head
head.is_empty (ET BOTCLAUSE); (3) Ht apply_head live.is_empty (ET DEADHEAD); (4) QoSat add_lit
complement (ET QOCLASH); (5) QoSat method apply_head head.is_empty (ET QOBOT); (6) QoSat apply_head
live.is_empty (ET QODEAD). NONE fire ⇒ the clash is raised in a 7th path: almost certainly
**eval_disj's disjunction-collapse** (a parked disjunction whose live set empties → DEval::Clash →
Scan::Clash, bypassing apply_head) OR a raise_clash in propagate/process_nominals not via add_concept.
NEXT: trace eval_disj (hypertableau.rs ~1560, the DEval::Clash return) + Scan::Clash in
next_action_incremental (~5466). Then diagnose whether layer B is a distinct bug or the same
self-loop/inverse family manifesting through a collapsed disjunction. ALL EDGETRACE/FIRE/clash-marker
diag edits are UNCOMMITTED (gated, on laptop+IBEX src): add_concept, add_edge, apply_head(free-fn x2),
add_lit, QoSat apply_head x2 — REVERT before any commit. The committed fix 592cf27 is clean (only the
two self-loop guards). Konclude confirms BFO_0000020 SAT (satisfiability -x ... = Yes).

**SESSION 6o FINAL — 7th clash site (eval_disj DISJCLASH) ALSO empty; layer B raised OUTSIDE all
standard clash paths.** Added eval_disj DEval::Clash trace (ET DISJCLASH) — STILL 0 markers across
ALL SEVEN sites, yet BFO_0000020 reported unsat. ⇒ the unsat is NOT a model clash through any of:
add_concept / apply_head(free-fn x2) / add_lit / QoSat-apply_head(x2) / eval_disj. So it is raised
via: (a) a direct `raise_clash(...)` call NOT in those sites (grep raise_clash callers), OR (b) an
`unsupported` (out-of-fragment) being MIS-REPORTED as unsat in the result mapping, OR (c) the
unsat-list construction in qo_classify / the tableau output logic (a concept listed unsat without a
model clash). NEXT diagnostic (fresh): trace `raise_clash` ITSELF (the chokepoint, ~892) with the
dep, AND inspect how `km tableau`/qo builds the `unsatisfiable` list (does `unsupported` → unsat? is
node_unsat set elsewhere?). DECISION: CONSOLIDATED here — `git restore`d the tree to 592cf27 (all 9
diag traces DROPPED, tree clean, synced ws+IBEX). The self-loop fix (592cf27) stands as the real
committed win (several concepts flipped SAT, 147/0). Layer B + layer C (shared-filler pollution)
remain for 10908's full solve. Total turn: ported Konclude blocking (mode-5), 3 specs, found+fixed
the self-loop soundness bug, deep-diagnosed layer B to "outside all 7 clash sites".

**SESSION 6p — FOLLOWED KONCLUDE'S ACTUAL STEPS via its debug dump (2026-06-25).** Konclude has
a Debugging config (Source/Config): `Konclude.Debugging.WriteDebuggingData` +
`WriteDebuggingDataCompletionTasks` + `WriteDebuggingDataForAllTests` + `BaseWritingPath`. Built a
dbg-config.xml (copy default-config.xml, insert those <Set key=..><Literal>true</Literal></Set>
before </RequestMessage>), ran `Konclude satisfiability -c dbg-config.xml -i 10908.owl -x
.../BFO_0000020` from a dir with ./Debugging/CompletionTasks/. RESULTS:
  - CompletionTasks dump EMPTY ⇒ Konclude decided BFO_0000020 SAT via SATURATION, NO tableau
    completion task ran (its laziness — never builds the model KM clashes on).
  - Preprocessing dumps written (1-Builded..5-ProcessedTBox.txt). Konclude's PROCESSED form:
    * ObjectHasSelf kept as NATIVE `CCSELF<role>` CONCEPTS: `97: CCSELF<BFO_0000083>`,
      `101: CCSELF<BFO_0000123>`; spatial(118): `CCSUB(|+97|...|+101|...)` ⇒ spatial ⊑
      CCSELF<located-in> ⊓ CCSELF<location-of> (self markers, NOT edge clauses).
    * inverse kept NATIVE: role 55(BFO_0000123) `inverse roles: -14(BFO_0000083)`,
      `domain concepts:+118(spatial)`, `range concepts:+151(BFO_0000004)`.
  THE DEVIATION (answer to "where do you deviate from Konclude"): the SEMANTICS MATCH
  (domain(location-of)=spatial, range=BFO_0000004, location-of⁻=located-in, spatial⊑CCSELF<self>);
  KM deviates at REPRESENTATION/CLAUSIFICATION — cb_to_ht compiles ObjectHasSelf into r(x,x) EDGE
  clauses (cid102 Q→r(x,x), cid103 r(x,x)→Q) and inverse into BRIDGING clauses (r1↔r40), and the
  interaction of those clausified forms over-derives. Konclude keeps both NATIVE (CCSELF concept +
  native inverse role) and decides by saturation. The self-loop matching bug (592cf27) was symptom
  #1 of KM's clausified Self. HOW TO FOLLOW KONCLUDE'S STEPS (reusable): the debug dump above; for a
  completion-task model dump pick a concept Konclude can't decide by saturation, or force
  WriteDebuggingDataForAllTests; writeGeneratedExtendedDebugIndiModelStringList dumps node+concept+
  edge model to ./Debugging/CompletionTasks/*.txt. NEXT for layer B: dump Konclude's
  AbsorbedTBox/saturation for BFO_0000020 and compare KM's per-rule derivation; the residual clash
  is another consequence of KM's clausified CCSELF/inverse (not the native form Konclude uses).

**SESSION 6q — LAYER B/C ROOT FOUND: it's the LEGACY-TABLEAU FALLBACK, not the fast Ht (2026-06-25,
job 47783312).** Traced 7 clash sites in hypertableau.rs — ALL EMPTY for BFO_0000020 — because the
clash is NOT in the fast Ht. Added a trace at consistent()'s return; the decisive line:
`ET CONSISTENT seed=[(false,11)] out=Sat unsupported=true nodes=6`. So the fast Ht builds a Sat
6-node model for BFO_0000020 (NO clash) but flags **unsupported=true** ⇒ consistent() returns None
⇒ classify's `?` propagates None ⇒ classify returns None ⇒ **run_json (tableau.rs ~4564) FALLS
THROUGH to the LEGACY `Tableau::new(clauses).classify()`** which is the documented-unsound reasoner
([[CLAUDE.md]] "Tableau is NOT a benchmark fallback") — IT emits the false-UNSAT. That is why
hypertableau.rs's raise_clash/kill_node never fired (the clash is in tableau.rs's Tableau).
**REFRAMES layers B AND C:** classify returns None on the FIRST unsupported concept (the `?`), so a
SINGLE unsupported query makes the WHOLE `km tableau` batch fall to the legacy Tableau → the 664
false-unsats are very likely the LEGACY TABLEAU, not shared-filler pollution. The fast Ht is SOUND
here (it correctly defers); the unsoundness is the fallback. WHERE KM DEVIATES FROM KONCLUDE: the
fast Ht BAILS `unsupported` at apply_head on a construct Konclude handles — almost certainly a
disjunctive head containing ∃/edge ("TR UNSUPPORTED: disjunctive head with exists/edge", ~1382) or
a mixed concept+Eq head (negative ≥n recognition, ~1290). Konclude's executeORBranching handles ∃
disjuncts fine. **FIX (the Konclude port the user wants): port OR-branching over ∃-disjuncts (and/or
the mixed concept+Eq ≥n head) into apply_head so the fast Ht doesn't bail** — then 10908's
unsupported concepts get a sound Ht answer instead of the unsound legacy fallback. Capturing the
exact bail reason via job 47783321 (KM_HT_TRACE TR UNSUPPORTED). Interim mitigation option: make
run_json NOT fall through to legacy Tableau (defer like KM_HT_QO_CERTIFY_ONLY) — avoids the wrong
answer but gives no answer (production routes 10908 to CB anyway; the forced-Ht is a test harness).
ALL diag traces (raise_clash/kill_node/consistent + the earlier reverted ones) UNCOMMITTED on
laptop+IBEX; git restore to 592cf27 before any commit.

**SESSION 6r — layer B bail CONFIRMED = apply_head:1293 mixed concept+Eq head (negative ≥n
recognition), "not yet supported" (2026-06-25, job 47783321).** KM_HT_TRACE grep for UNSUPPORTED
was EMPTY ⇒ the bail site prints no trace. Of the Ht apply_head unsupported sites (1287 qmerge-off,
1293 mixed-Eq, 1340 head-Eq[traced], 1378 disj-∃[traced], 1413/1464 HUGEMATCH[traced]), with
KM_HT_QMERGE=1 the only reachable UNtraced one is **line 1293**: after the all-Eq ≤n branch, a head
with BOTH Concept AND Eq atoms (= negative ≥n recognition, number=true) → `ext.unsupported=true`.
So BFO_0000020 (number=true) produces a ≥n-recognition mixed head, the fast Ht bails unsupported →
None → legacy-Tableau fallback → false-UNSAT. **THE KONCLUDE PORT FOR LAYER B = support the
mixed concept+Eq head (negative ≥n recognition) in apply_head — the ≥n at-least rule
(createDistinctSuccessorIndividuals 16140: create n distinct successors + pairwise distinctness;
KM already emits ≥n as distinct ∃ + ⊥⟵Eq distinctness clauses, so the gap is the RECOGNITION head
`...∧≥n-concept → ⋁Eq ∨ ...`).** Decisive trace recipe (reusable): add `ET CONSISTENT seed out
unsupported nodes` at hypertableau.rs consistent() return (~6306) — shows the fast Ht builds a Sat
model but flags unsupported; the false-UNSAT is the tableau.rs legacy `Tableau::classify` fallback
at run_json ~4567. Tree clean at 592cf27 (diag reverted, synced ws+IBEX). NEXT: port the ≥n
recognition head into apply_head (synthetic-test it), which should make BFO_0000020 (and the ≥n
family of the 664) resolve in the sound fast Ht instead of the unsound fallback; interim sound
option = make run_json defer instead of falling to legacy Tableau.

**SESSION 6s — ≥n recognition rule PORTED + committed 3002f2c (2026-06-25).** Layer B done:
apply_head's number+Eq block now handles the MIXED concept+Eq head `Q(x) ∨ ⋁ yi≈yj` (the
contrapositive of `≥n r.F ⊑ Q`) instead of bailing `unsupported` at the old line 1293. Design =
ONE deferred cardinality choice unifying ≤n AtMost + ≥n recognition: `MergeDisj` gained
`concepts: Vec<(Node,CLit)>`; `push_card(concepts,pairs,bdep)` (push_merge = empty concepts, ≤n
path BYTE-IDENTICAL); apply_head collects live/dead recognized concepts + candidate pairs, asserts/
merges a single live option, defers ≥2 to `branch_merge` which branches over BOTH option kinds
(assert-concept | merge-pair), recomputing liveness at branch time; `next_merge` treats a present
recognized concept as satisfying. `Ht::set_number(on)` (force_number, re-applied per Ext rebuild,
also forces qmerge) wired in run_json from inp.number so a number KB routed to the fast Ht runs the
cardinality rules. 3 synthetic tests (dead-merge→unit-merge-clash unsat; mixed 2-opt branch asserts
Q→both clash unsat; Q-branch→sat) + 150 hypertableau tests pass, 0 regress. NEXT for 10908 end-to-
end: sound inverse (task #11; 10908 has inverse, reaches fast Ht only via KM_HT_FORCE) + native
CCSELF; + make run_json DEFER (not legacy-Tableau fall-through) on any residual unsupported. NOT
yet ORE-validated (build-first rule): full corpus run pending the inverse piece.

**SESSION 6t — 10908 FINALIZED gold-MATCH (IBEX job 47783535, 2026-06-25).** The ≥n recognition
rule (3002f2c) + self-loop fix (592cf27) SOLVE 10908 in the fast Ht: status=ok, gold=MATCH,
unsound=0, incomplete=0, 42.9s, 4.5MB peak (KM_HT=1 KM_HT_FORCE=1 KM_HT_QMERGE=1, mode-1 blocking).
CRUCIAL CORRECTION: ht_features reports **has_inv=FALSE** for 10908 — it is SHOQ (number+nominal,
NO inverse). All the prior "10908 needs inverse/NN-rule" analysis was WRONG; inverse was never the
blocker. The recognition rule (mixed concept+Eq head) + self-loop matching were the whole fix.
BONUS: **15672 also gold-MATCH** (1.5s, 15.4MB) — a live-disjunction-family target, now exact via
the same build. 10621 STILL timeout@300s (244385 clauses / 81749 concepts — pure SCALE, n_disj=179;
separate throughput problem, not correctness). NEXT per standing /goal: full-corpus benchmark
through the fast Ht (route SHOQ/number no-inverse onts via KM_HT_NOMINALS + recognition rule) to
measure passrate/time/mem vs gold and confirm 0 regression. ht_runone.py is the per-ont tool
($KM/engine binaries, HT flags from env, vs gold). NB build on IBEX compute node (build.sbatch
builds only kobayashi-marust; my finalize sbatch builds ofn+tableau_cli+elc too).

**SESSION 6u — 10621 ROOT-CAUSED = DATATYPE ont, fast Ht is WRONG engine (2026-06-25).** Chased
10621 timeout to its root. NOT scale/convergence, NOT a number/nominal bug. The fast Ht (forced
via KM_HT_FORCE) wrongly derives many NAMED anatomy concepts (Fibrous_sheath_of_index_finger,
Abdominal_wall, ...) as UNSAT, each building 6-50k-node spurious deterministic models (the timeout
cause). Konclude gold = consistent, 0 unsat concepts (job 47785183). CLASHTRACE (gated diag, since
reverted) pinned the clash to empty-head clause `__dt__val__"false"^^xsd:boolean ⊓
__dt__val__"true"^^xsd:boolean → ⊥` (tin cids 8178/1426): a node ends up as BOTH boolean true and
false. 10621 is a DATATYPE (boolean data-property) ontology; the fast Ht has NO concrete-domain
oracle, so cb_to_ht encodes datatype values as opaque pairwise-disjoint concepts and the Ht derives
spurious clashes. The datatype oracle lives in the CB engine (data_abox/datatypes), which is where
10621 routes in PRODUCTION — but CB TIMES OUT (240s/5.6GB; hyb-fallback + cb-orderedall both
timeout). So 10621 = (a) Ht can't do it (no datatypes, unsound if forced) + (b) CB right-engine but
scale-bound. ROUTING-CORRECTNESS NOTE: ht_runone `routable` guard = dropped==0 ∧ ¬fenced ∧ ¬inverse
— does NOT exclude datatypes, so the forced-Ht corpus sweep (47783564) wrongly routed datatype onts
to the Ht (they mostly TIMED OUT rather than gave wrong answers, so the 503-MATCH/0-new-unsound
conclusion stands; recognition rule is orthogonal+sound). The faithful paths for 10621: (1) fence
datatypes from Ht routing (small, correct, but doesn't classify it) + scale the CB datatype engine
(large), or (2) add a concrete-domain oracle to the Ht (large). NOT a tableau-mechanism port.

**SESSION 6v — 10621 FULLY root-caused = deterministic over-derivation surfacing via functional
boolean datatype (2026-06-25).** VERIFIED Konclude AND ELK both say 10621 CONSISTENT, 0 unsat (jobs
47785183, bigsweep sigs) → KM's unsat is a definite bug, NOT contested gold. Drilled the clash
(gated KM_HT_CLASHTRACE, reverted): empty-head disjointness `__dt__val__"true"^^xsd:boolean ⊓
__dt__val__"false"^^xsd:boolean → ⊥` fires on a data-value node (e.g. 653) that is the SINGLE
`has_mass` successor (role 61 = has_mass, FunctionalDataProperty) of an anonymous part_of-chain
object node (e.g. 229). Node 229 has accumulated 138 positive classes deterministically
(branch_pushes=0) incl. Material_physical_anatomical_entity (⊢ has_mass=true via Anatomical_structure
⊑ Material) AND a has_mass=false class. The ont has ZERO explicit DisjointClasses (559
EquivalentClasses, 5199 ObjectUnionOf); Material vs Non-material are disjoint ONLY implicitly via
functional has_mass. So KM over-derives: it forces an anonymous successor to be BOTH material and a
has_mass=false class without the disjunction branch that would keep it consistent — Konclude does
not. This deterministic ∀-accumulation over part_of/member/bounds/regional_part chains is BOTH the
soundness bug AND the model-explosion (6-50k nodes)/timeout cause. NOT a missing-Konclude-mechanism
port and NOT a datatype-encoding bug (stripping value-singleton clauses + nominals both inert); the
datatype just SURFACES an object-domain over-derivation. ASSESSMENT: deep, calculus-touching
(∀-propagation/union handling) → Lean re-cert; multi-session; fast Ht is structurally wrong for
datatype onts (CB has the oracle but times out 240s/5.6GB). The 10908+15672 wins stand
(orthogonal). Diagnostic infra: KM_HT_CLASHTRACE pattern (clash node + in_edges + pred label),
map ids via tin concepts/roles arrays. ~19 IBEX jobs 47783535..47786978.

**SESSION 6w — 10621 is CONTESTED GOLD; KM is CORRECT, Konclude gold is WRONG (2026-06-25, PROVEN).**
COMPLETE REVERSAL of 6u/6v. The "spurious unsat" is GENUINE unsat. Traced KM's clash to: anonymous
regional_part successor node is BOTH Anatomical_structure (->Material->has_mass=true) AND Zone_of_cell
(->has_mass=false). The OWL has the TOLD chain Zone_of_cell ⊑ Fiat_cell_part ⊑ Fiat_anatomical_structure
⊑ Anatomical_structure ⊑ Material_physical_anatomical_entity ⊑ DataHasValue(has_mass,true), PLUS
Zone_of_cell ⊑ DataHasValue(has_mass,false), PLUS FunctionalDataProperty(has_mass). => Zone_of_cell ⊑ ⊥,
airtight OWL DL. PROVEN on a minimal extracted ontology (job 47787383): **HermiT 1.4.6 says
"Classes equivalent to owl:Nothing: Zone_of_cell"**; KM CB engine says `unsatisfiable: [Zone_of_cell]`.
Konclude gold for 10621 = consistent, EMPTY #UNSAT block (0 unsat) => WRONG. ELK = consistent + says
Zone_of_cell ⊑ Anatomical_structure but CANNOT see the functional-datatype unsat (EL profile). So the
contested-gold authority HermiT AGREES WITH KM (matches the known pattern [[project_km_contested_gold]]:
HermiT right, Konclude ORE gold wrong on datatypes). 10621 belongs with 8941/13912/15516/2669 as
contested gold. CONSEQUENCES: (1) NO KM soundness bug — KM (CB and Ht) is sound on 10621. (2) There is NO
"Konclude method" to port — Konclude is incorrect here. (3) 10621 can NEVER MATCH this gold; it should be
EXCLUDED/regold (use HermiT). (4) The Ht "timeout" is KM doing CORRECT-but-expensive unsat proofs (many
FMAInOWL concepts are genuinely unsat via functional has_mass/has_boundary + Material/Non-material chains);
the recognition-rule sweep's 10621 timeout is therefore not a soundness concern. Full-HermiT cross-check
on whole 10621 = job 47787393 (in flight) to quantify the genuine-unsat count + confirm
Fibrous_sheath_of_index_finger. Diagnostic chain: clash node -> pred label -> ELK/Konclude subsumer diff
-> told-axiom chain -> minimal-ont HermiT proof. ~24 IBEX jobs 47783535..47787393.

**SESSION 7 (2026-06-25) — TWO durable findings + workflow correction.**
(1) **PRODUCTION-WIRING GAP for the 10908/15672 wins.** The recognition rule (3002f2c)
+ self-loop fix (592cf27) + nominal o-rule (38cf4c9) solve 10908/15672 in the fast Ht
ONLY via the STANDALONE worker (`tableau_cli` on a dumped TIN, or ht_runone) with
KM_HT_NOMINALS+QMERGE+EAGER+NEGTRIED+ORD=1+BLOCKSKIP+incr. Reproduced on ws: 15672
standalone = **4.76s / 15.4MB, 142 subs (consistent, =gold)**. BUT `km classify` (the
orchestrator) TIMES OUT on them: race.rs `ht_routable` REJECTS nominals+inverse
(line 431) and `qo_candidate` requires nominals empty, so spawn_ht never routes SHOQ
onts to the fast Ht (only KM_HT_FORCE does); and even forced, the FALLBACK race waits
~225s for the doomed CB before taking the ready HT answer (the 7581 fallback-budget
issue). So the wins are NOT yet in the real pipeline. tableau.rs run_json line ~4504
DOES route SHOQ to fast Ht when KM_HT_NOMINALS set (calls set_nominals+set_number),
but the ORCHESTRATOR gate upstream blocks it. Bounded fix = a sound SHOQ/number
no-inverse no-datatype route in race.rs (fallback mode = sound-by-construction modulo
fast-Ht soundness) — task #13.
(2) **The fast Ht is SOUND but NOT robustly COMPLETE/TERMINATING on the broader nominal
fragment.** Trustworthy ws check (named-only filter via ofn iri_map+named; reflexive
X⊑X are gold-omitted artifacts, not unsoundness): 10242 (148 noms) unsound≈0 BUT
classifying the TIN's query subset (3722/5541 named) leaves big apparent incompleteness,
and forcing queries=ALL 4551 concepts HANGS (non-convergent nominal concept). 10594
(158 noms) same. So SHOQ→fast-Ht is NOT a blanket-safe production route — it solves the
specific small SHOQ targets (10908/15672) but hangs when fully classifying heavy-nominal
onts. Implication: wire SHOQ→fast-Ht in FALLBACK mode only (fills CB timeouts, CB
preferred when it finishes); do NOT race-prefer the fast Ht on nominals (incompleteness/
non-termination risk).
(3) **WORKFLOW (user HARD steer 2026-06-25):** run TARGETED evaluation (few onts) on
**ws**, NOT casual full IBEX sweeps; use **unimatrix01** for a full sweep but RARELY.
Cancelled IBEX full sweep 47787897. ws has a 60-ont nominal subset at ~/nomval/onts +
gold ~/nomval/gold + ore_canon.py; `km classify` is pure-Rust (no cb_to_ht.py needed);
build on ws (binary current Jun25, 150 tests pass). Targeted-ws checker scp'd to
ws:~/nomval/htchk2.py (ofn→named+iri_map; KM_DUMP_TIN→TIN; tableau_cli forced Ht;
named-only vs-gold diff). The big remaining port stays task #14 (sound non-shared-∀
saturation / lever C per docs/THROUGHPUT-SATURATION.md — the ONLY blocker for the
near-Horn SRIQ giants is ∀-shared-filler pollution; mechanisms all else already present
per 6f/6g). See [[project_km_throughput]] [[project_km_konclude_study]].

**SESSION 7b LANDED — SHOQ→fast-Ht production route committed (3789368, KM_HT_SHOQ,
default OFF).** The 10908/15672 wins are now realised in the real `km classify`
pipeline (were standalone-only). race.rs `shoq_candidate` = faithful ∧ ¬datatype
(has_datatype scans clauses for `__dt__val__`) ∧ nominals≠∅; nominal-presence is the
separator from the unsound number-only SRIQ giants (9724/7914 nominals=0). Sets
KM_HT_NOMINALS+KM_HT_QMERGE, fallback mode (monotone-safe, CB preferred).
**CRITICAL ROOT-CAUSE FOUND: the parallel per-concept classify (KM_HT_PAR>1) is
UNSOUND with the nominal o-rule** — nominal merges are GLOBAL state, parallel workers
race → false-UNSAT (10908: 86 of 6001 subs at PAR=8 / TIMEOUT for 15672; both gold-exact
single-threaded). The route forces KM_HT_PAR=1 (and a `&& !shoq_candidate` guard stops
spawn_ht's default KM_HT_PAR=avail_cpus from overriding it). NB the EARLIER belief that
15672 needs EAGER+BLOCKSKIP was a pre-fix artifact: with recognition+self-loop+o-rule in
the binary, plain NOMINALS+QMERGE (mode-1, PAR=1) gives 10908 6001/6001 (0.22s) + 15672
142/142 (3s) standalone; the search-discipline flags are harmless but unnecessary here.
VALIDATED on ws (km classify vs gold, group-safe single-thread): 10908 MATCH, 15672 MATCH,
canaries 10242/10594 MATCH (CB-fallback, 0 regress); 150 tests. PROMOTION to default-on
pending a rare full-corpus soundness sweep on unimatrix (the gold rule [[feedback_ws_no_orphans]]:
targeted on ws, full sweeps rare on unimatrix). Reverted a stray gated KM_HT_CLASHTRACE
diag in hypertableau.rs before commit. Tools: ws ~/nomval/{clsval.py(group-safe km classify),
htchk3.py(standalone tableau_cli on a dumped TIN)} — both via ore_canon.canonicalize.

**SESSION 7c — LEVER C grounded + next increment pinned (2026-06-25).** Re-read the
QoSat saturation in hypertableau.rs. P2.1 (KM_HT_QO_SHIQ) ALREADY builds the SOUND
non-shared successors: apply_head ∃-case (~4370) creates a successor OWNED by the source
(`qo_parent[f]=n`, is_filler[f]=true), so `∀R.C` (the t!=X concept-head write ~4323) lands
on an independent node with NO critical-ALL pollution (the `self.shiq` branch ~4329 skips
`qo_insufficient`), bounded by ancestor subset blocking `qo_blocked` (~4384, B1: label[n]⊆
label[ancestor] up the qo_parent chain). ensure_filler (~3256) is the OLD shared
(filler,role)->node path used only when !shiq (the pollution source). DECISIVE TRADEOFF
(re-confirmed from code+docs): the GLOBAL single pass holding all concepts' non-shared
trees is ×concepts MEMORY (27GB OOM on 7914 — blocking bounds DEPTH not BREADTH);
PER-CONCEPT is memory-fine (~490MB) but too SLOW (successor subtrees not reused across
the ~17-58k concepts). **THE next increment = content-addressed SUCCESSOR-SUBTREE
saturation cache: saturate a successor's subtree ONCE keyed by its full INITIAL forced
label (filler concept + the ∀-operands pushed onto it before its own expansion), reuse
across every concept that builds a successor with that exact label.** This is DISTINCT
from the self-node (concept,neg) cache 6g found inert (that was the SHARED global pass;
non-shared per-concept subtrees genuinely RECUR across concepts → real hit rate). Sound
because the key captures ALL forcing of the subtree. Build incrementally on ws w/ synthetic
tests; this is the Konclude tryEstablishSaturationCaching analogue on the P2.1 non-shared
pass. Realistic scope: multi-session (the shiq_build "orders of magnitude" finding stands;
this is the lever that could close it). Do NOT rush unsound cache code at turn-tail.

**SESSION 7d CORRECTION — 7c's "successor-subtree cache" was INVENTED; the FAITHFUL
Konclude mechanism is G2/G3 status-flag criticality (read the source, per user rule).**
Read CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp on the laptop
(Public/software/Konclude/Source/Reasoner/Kernel/Algorithm/). Konclude has NO subtree
cache — its shared C-nodes (one per concept/polarity, ∃ reuses them) ARE the
amortization. The ∀-rule `isCriticalALLConceptDescriptorInsufficient` (:3451) CHECKS
whether each R-successor's label already contains the ∀-operands
(`succConSet->containsConcept` :3517) and NEVER writes them into the shared filler; a
miss marks the SOURCE node INSUFFICIENT (:881 updateDirectAddingIndividualStatusFlags
INDSATFLAGINSUFFICIENT) and propagates by STATUS FLAG not label
(`updateIndirectAddingIndividualStatusFlags(n, succ->getIndirectStatusFlags())`
:1657/1803/1939/2018). 3-state CLEAN/CLASHED/INSUFFICIENT; INSUFFICIENT→residue tableau.
**KM ALREADY HAS this = KM_HT_QO_KPSET (kp_check_head/kp_finalize = the containment
check; qo_insufficient apply_head:4331; kp_insuff_nodes).** The wall is it OVER-DEFERS
on inverse-heavy giants (kp_miss 930k/66M → ~0% clean → global deferral). FAITHFUL fix
(NOT a new cache): make G2/G3 propagation PRECISE — (1) propagate insufficiency only
along genuine FORWARD predecessor links, not the conflated reversed inverse back-edges
(KM's reverse-reach over-marks); (2) port the per-creation-role ALL-concept extension
(getRoleSuccessorALLConceptExtensionData :960 / CSaturationLinkedSuccessorIndividual
ALLConceptsExtensionData) so ∀-operands live in a SEPARATE struct for the criticality
check, NOT in the shared subsumer label; (3) backward named-subsumer write to the
predecessor (addConceptFilteredToIndividual :1235) kept distinct from the forward
operand check. Plan rewritten in docs/LEVER-C-CACHE.md (commit 814da39). Build steps:
regression test → port #1 (forward-only insuff propagation, measure clean% rises from
~0 on 7581/9724) → port #2 (separate operand extension) → isolated 7914/9724 measure →
rare unimatrix sweep + Lean. Multi-session.
