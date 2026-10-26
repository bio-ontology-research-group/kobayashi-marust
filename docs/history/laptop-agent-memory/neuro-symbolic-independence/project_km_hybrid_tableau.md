---
name: project_km_hybrid_tableau
description: "KM hybrid CB+hypertableau build — ALC+RBox+SH+SHI+SHQ validated vs HermiT (M2 number restrictions done); nominals fenced; Konclude source unavailable, built from papers"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

M2 STATUS (2026-06-07): NUMBER RESTRICTIONS done + validated (SHQ); nominals fenced.
- `≥n R.C`: encoded as n existentials with pairwise-disjoint fresh `__slot__f` fillers
  (driven by moose's `q∧≈(fᵢ,fⱼ)→⊥` distinctness pairs) — reuses ∃+Horn-clash, NO
  inequality relation. `≤n`/functional: new `eq` head atom → tableau MERGES the two
  nodes. n=1/functional = deterministic merge in horn_saturate; n≥2 = Hyp branch over
  pairs. Merge = union-find (`Graph.repr`, lower id survives, edges+pred rewritten,
  reads canonicalise via `find`). Blocking: subset is UNSOUND with number → `number`
  flag switches to EQUALITY blocking (L(s)=L(t), SHQ-sound). `expand` gains a
  number-only branch. `inverse∧number` (SHIQ) FENCED (merge×pairwise not validated);
  inverse-functional FENCED; plain functional un-fenced.
- Files: engine/py/cb_to_ht.py (convert: distinct_pairs→slots, eq_clauses→eq heads,
  `number` flag, `__nom__` + SHIQ fences), engine/py/frontend.py (un-fence functional,
  parse ObjectHasValue=∃R.{a}), engine/src/tableau.rs (Atom::Eq, Graph.find/alive/merge,
  number field+set_number, equality-blocking branch, eq in head_atom_present/add_head_atom,
  number-only expand path, JAtom::Eq, TInput.number). 5 new Rust tests, all 30 pass.
- VALIDATED 0 MISMATCH vs HermiT: 4 .ofn fixtures (card_ge_le_unsat, card_ge_sub,
  card_qual_unsat, functional_unsat — committed + results/*.json); 5 REAL ALCQ slices of
  ore_ont_10140 (the only pure-SHQ ORE ont, cardinality block lines 117400-134000):
  442/867/1700/3860/3726 subs all exact. Full 10140 (142k concepts/355k clauses) out of
  budget — but HermiT ALSO times out >400s, so it's the #26 scaling gap not a bug;
  consistency+1-concept over full TBox = 1.1s (merge machinery scales).
- NOMINALS: was a SILENT bug — `__nom__a` passed as a free concept (dropped the singleton
  constraint). Now FENCED honestly (cb_to_ht detects `__nom__` concepts; ObjectHasValue
  parses so it fences not crashes). Full nominal reasoning (cross-branch at-most-one merge
  — union-find already supports it — + NI-rule + termination) = task M2c, DEFERRED (no SHOQ
  validation target in sample; must not ship unsound).
- NEXT: task #26 large-ontology scaling (true semi-naive + shared TBox closure) — the
  lever that would make ore_ont_10140 and the borderline 1017 classifiable.

GOAL (user, 2026-06-06): build a HYBRID consequence-based + hypertableau reasoner
in Rust to beat KM's live-disjunction timeouts (Konclude-competitiveness). Decision
followed the definitive finding that ALL pure-CB levers fail on those cases (see
[[project_km_reasoner_perf]]) — the gap is architectural (tableau explores ONE
model, CB saturates ALL consequences).

KONCLUDE SOURCE IS NOT PUBLIC: the github.com/konclude/Konclude repo (master + all
release tags) ships only build Configs + External third-party libs + binaries — ZERO
.cpp source. So we build from the calculus PAPERS, which is the right foundation
anyway. Key local papers: papers/dl/msh09-hypertableau-JAIR.pdf (THE hypertableau
calculus HermiT implements), bate-cuenca-grau-motik-2016-extending-CB-SRIQ.pdf (CB→
SRIQ, the hybrid direction), tena-cucala-2018 (KM's CB calculus).

DESIGN (full spec in kobayashi-marust/docs/HYBRID-TABLEAU.md):
- KM already has the deterministic HALF in disguise: its DL-clauses ARE hypertableau
  clauses; Pred/Succ edges ARE the completion-graph skeleton; Bate's completeness
  proof IS the model-construction algorithm.
- HANDOFF = per-context, threshold-triggered (NOT per-candidate-subsumption, which
  throws away CB's one-pass classification). CB saturates the Horn/deterministic
  closure; when a context's LIVE disjunctions exceed a threshold, FREEZE it and hand
  core_v + frozen clauses + boundary (Pred/Succ) constraints to a hypertableau;
  tableau returns UNSAT+clash-core (→ context clause Γ'→⊥) or SAT+branch-invariant
  atoms (→ Horn clauses Γ→A). Cache SAT/UNSAT per (core_v, clause-subset). Nominal
  caveat: root/v_r interaction is global, exclude from caching or pass root
  constraints in.
- ONE divergence to resolve: KM's moose normaliser PRE-SKOLEMIZES ∃ (f(x));
  hypertableau keeps ≥n R.B un-Skolemized and generates successors at RUNTIME via the
  ≥-rule (blocking needs this). Plan: add an HT-clause emit mode to moose.

STAGED PLAN: M1 standalone ALC hypertableau consistency checker (covers stress test +
541) → M1b inverse+transitive (pairwise blocking) → M2 number restrictions+nominals
(≤-rule, NI-rule) → M3 hybrid integration (liveness threshold + feedback clauses +
per-context cache) → M4 certification (per-run soundness cert + Lean completeness).

STATE 2026-06-07 (M1 proof-of-concept VALIDATED + two hardening gaps found):
- Driver done: tableau.rs has JSON I/O (TInput: concepts/roles/clauses/queries) +
  classify (O(n²) A⊓¬B checks) + run_json; new bin src/bin/tableau_cli.rs.
- CB→HT converter engine/py/cb_to_ht.py: REVERSE-SKOLEMIZATION of moose CB clauses
  (a function f with `Body→r(x,f(x))`+`Body→C(f(x))` becomes `Body→∃r.C(x)`); all
  other CB clauses are ALREADY HT form (∀ via guarded y, disjunctions, definers).
  Reuses the whole moose pipeline. Pipeline: owl→frontend.ofn_to_clauses→cb_to_ht→
  tableau_cli.
- VALIDATED vs HermiT (local jar at ai-biomed-summer-school/.../gateway/lib, run via
  oracle/Oracle.java): stress test B_i≡∀r.(C_i⊔C_{i+1}) — tableau MATCHES HermiT at
  every N and FINISHES where CB times out (N=40: tableau 9.3s, HermiT 1.9s, CB
  TIMEOUT; N=60: 42.7s/3.6s/TIMEOUT). Plus tiny.ofn + alc1.ofn (exact: transitive
  subsumption, reverse-Skolemized ∃ entailment, union equiv, disjointness-unsat).
  Thesis PROVEN: model-building beats CB saturation on live disjunctions.
- BATCH on 40 real ORE onts EXPOSED TWO M1-HARDENING GAPS (honest):
  (1) **Converter silently DROPS the RBox.** moose handles role hierarchy r⊑s,
  domain, range, inverse, transitivity via the CB ENGINE's trigger machinery +
  augment, NOT as concept-clauses — so cb_to_ht never sees them. Confirmed on
  ore_ont_10199 (60 role-head clauses all Skolem, 0 `r⊑s` clauses; tableau misses
  Animal⊑Scientist via Animal⊑∃r.B, r⊑s, domain(s)=Scientist). Violates
  no-silent-approximation. FIX: emit RBox as HT-clauses (domain(r,D)→r(x,y)→D(x),
  range(r,C)→r(x,y)→C(y), r⊑s→r(x,y)→s(x,y), inverse/transitive=M1b) from the OWL
  RBox or moose hooks; until then FLAG RBox as out-of-fragment. Better long-term: a
  faithful HT normaliser in moose (CB clauses are lossy on RBox).
  (2) **Perf:** 20/26 in-fragment ORE onts TIMEOUT@30s. O(n²) classify × per-step
  full rescan + clone-on-branch doesn't scale; needs told-subsumer classification,
  indexed/incremental rule application, trail backtracking.
  So M1 = validated PROOF-OF-CONCEPT, not yet a practical classifier. Local HermiT
  classpath: /home/leechuck/Documents/papers/ai-biomed-summer-school/notebooks/mowl/
  gateway/build/distributions/gateway/lib/*. ORE sample at /tmp/oresample/.

RBOX FIX DONE 2026-06-07 (gap #1 closed, converter-side only — tableau.rs UNCHANGED
so Lean cert still holds):
- frontend.py: new `ofn_rbox(path)` reads RBox straight from the parsed functional
  syntax (same s-expr parser, NO regex) incl. domain/range that moose's add_axiom
  drops. Returns records: subrole/domain/range (in-frag) + ("fenced",reason,detail)
  for inverse/transitive/symmetric/reflexive/functional/role-chain/complex-dom-range.
  frontend __main__ now emits {"clauses":..,"rbox":..}.
- cb_to_ht.py: `main` refactored to `convert(clauses, rbox=None)`. Emits in-frag RBox
  as Horn HT-clauses: r⊑s→r(x,y)→s(x,y); range(r,C)→r(x,y)→C(y); domain(r,D)→backward
  edge clause r(x,y)→D(x) (SOUND: only asserts D where r has a successor). Blocked-node
  gap (∃r obligation never realised) recovered by DOMAIN-OBLIGATION PROPAGATION: each
  existential clause Body→∃r.fil also emits Body→D(x) for D in domain of r OR any
  super-role (reflexive-trans subrole closure). All Horn, no branching. `fenced` list
  surfaced in TInput so driver marks ontology OUT-OF-FRAGMENT (no silent drop).
- KEY DESIGN REJECTION: the "blocking-safe" GCI encoding domain≡⊤⊑D⊔∀r.⊥ adds a
  per-node disjunction per domain role (36 in 10199) ⇒ 2^36 branches/node ⇒ timed out
  even a single subsumption check. Horn edge clause + obligation propagation is the
  cheap sound+complete alternative. (Backward edge clause is SOUND not unsound: it only
  adds justified D; it's merely incomplete on blocked nodes, which the propagation fixes.)
- VALIDATED vs HermiT: ore_ont_10199 MISMATCH→MATCH (Animal⊑Scientist exact);
  ore_ont_10056 MATCH 1067 subs; new committed regression oracle/ontologies/
  rbox_domain.ofn (+results/rbox_domain.json). New harness oracle/validate_ht.py
  (full pipeline frontend→cb_to_ht.convert→tableau_cli vs HermiT; fenced/dropped⇒
  OUT-OF-FRAGMENT). ORE batch now honestly FENCES inverse/transitive/symmetric/chain
  onts (were silently-dropped-and-lucky before). Datatype onts (DataExactCardinality,
  ObjectHasValue,...) surface as CBERR from moose normaliser (separate frontend gap).
TRANSITIVE ROLES UN-FENCED 2026-06-07 (SH fragment, partial task #23):
- moose's TBox normalise ALREADY encodes transitivity losslessly as __trans__r__C
  propagation concepts in the concept-clauses (e.g. B(y),r(x,y)→__trans__r__C(x);
  __trans__r__C(y),r(x,y)→__trans__r__C(x); __trans__r__C(x)→Q). Converter passes them
  through. So frontend.ofn_rbox now does NOT fence TransitiveObjectProperty (just a
  `pass`). Subset blocking is sound for SH (transitive+hierarchy, NO inverse); onts
  with inverse/symmetric still fenced by those (SHI needs pairwise=M1b).
- VALIDATED exact vs HermiT, committed fixtures oracle/ontologies/{trans_test,
  trans_block,trans_hier}.ofn (+results): trans_block's Inf⊑Win needs transitivity AND
  blocking-active infinite chain together; trans_hier is transitivity THROUGH r⊑s
  hierarchy. ORE: un-fenced 6 onts into in-fragment (OUT-OF-FRAGMENT 21→15).

PERF PARTIAL 2026-06-07 (task #25, tableau.rs — perf-only, verdicts identical):
- classify() rewritten: was brute O(n²) {A,¬B} sweep. Now builds ONE model per {A}
  (find_model returns the Graph) and confirms only named concepts present in M_A's
  root label (a subsumer holds in EVERY model ⇒ in M_A; never outside). expand() now
  returns Option<Graph> not bool. 7 tests pass; all fixtures + 1067/437/106-sub
  matches unchanged.
INDEXED SATURATION DONE 2026-06-07 (task #25 main lever, tableau.rs, perf-only,
verdicts identical, 20/20 tests pass):
- Replaced deterministic_step (returned after ONE fact → outer loop re-scanned all
  clauses from idx 0 PER FACT) with saturate(): applies ALL Horn consequences per pass,
  loops to fixpoint, Horn fully before each ∃ round (blocking still sees complete
  labels). expand() now: saturate → find_disjunctive branch.
- Added per-clause predicate-presence INDEX: Graph.present_lits/present_roles (maintained
  via add_concept/add_edge), ClauseInfo precomputes body_lits/body_roles, matchable()
  skips any clause whose body needs an absent concept-lit/role (most of 3522 early on).
- EFFECT (full classify exact vs HermiT): ore_ont_1017 (1918 con/3522 cl) >90s TIMEOUT
  → 26s/1852 subs; 10160 TIMEOUT → 13s/7107 subs. All fixtures + prior matches unchanged.
- ORE batch FINAL v5: MATCH=9 MISMATCH=0 OUT-OF-FRAG=15 TIMEOUT=9 CBERR=7. 9 matches
  exact incl 10134(6794),10146(8813),10160(7107),10162(5474),10056(1067),10133(985),
  10174(437),10176(106),10199(1). Progression MATCH 5(pre,1 wrong)→4(RBox)→7(prune)→9
  (indexed). Remaining timeouts: 1017 borderline(26s), 10248 hard(165k cl).
- REMAINING: very large onts (10248: 67k con/165k cl) still over budget. Next lever =
  true semi-naive (drive from the newly-added fact, not re-run match_body per triggered
  clause) + share TBox deterministic closure across the n per-concept checks.
- GIT: tagged cb-only-final on e0f6e34 (last pure-CB commit, no tableau tracked) at user
  request — shippable standalone CB reasoner. All hybrid work still UNCOMMITTED on top.
- tableau still HermiT-validated not Lean-cert yet (M4).

M1b INVERSE ROLES 2026-06-07 (task #23, SHI — SOUND, termination caveat):
- moose does NOT encode inverse in clauses (unlike __trans__); InverseObjectProperties
  link is RBox-only. frontend.ofn_rbox now returns ("inverse",r,s); cb_to_ht emits BOTH
  edge dirs as clauses r(x,y)→s(y,x) & s(x,y)→r(y,x) (existing role-match navigates
  inverse, no engine change for navigation) + sets TInput.inverse=true.
- tableau.rs: subset blocking UNSOUND w/ inverse (blocked node's label flows back up via
  inverse edge). Added PAIRWISE (double) blocking, gated on inverse flag (else keep subset
  for speed). node_blocked: blockable s w/ parent p blocked by blockable strict-ancestor
  s2 w/ parent p2 iff L(s)=L(s2) AND L(p)=L(p2) AND edge_label(p,s)=edge_label(p2,s2) AND
  edge_label(s,p)=edge_label(s2,p2). Graph.edge_label(a,b)={roles on a→b}. Tableau.pairwise
  field + set_pairwise(); run_json sets from inp.inverse. 20/20 tests pass.
- VALIDATED exact vs HermiT: ore_ont_10026(1774 subs,0.12s), 10123(11516 subs!,19.9s);
  committed fixture oracle/ontologies/inv_test.ofn (A⊑C via ∀r⁻). Non-inverse onts
  unaffected (inverse=false→subset).
- TERMINATION FIXED via LOOP-BACK ∃-RULE (task #27, 2026-06-07): equality blocking alone
  does NOT terminate on ∀r⁻-over-infinite-chain (A⊑∃r.A, A⊑∀r⁻.D) — backward ∀r⁻ lags 1
  node behind ∃-frontier. Fix (pairwise path only): ∃-rule is a CHOICE — satisfy ∃r.fil by
  LOOPING BACK to an ancestor t (fil∈L(t), L(s)⊆L(t)) → cyclic model, with fresh successor
  as fallback branch. Loop-back-first collapses the infinite chain to a tiny cyclic model;
  fresh fallback keeps COMPLETE, saturation keeps SOUND (bad loop-back just clashes). expand()
  splits: inverse-free → fast batched saturate (unchanged); inverse → horn_saturate +
  disjunction-branch + loop-back-∃-branch (first_unsat_exists/loopback_targets helpers).
  VALIDATED: inv_block.ofn timeout→0.00s exact vs HermiT (now committed fixture); 10026/10123
  unchanged-exact, 10123 even faster 19.9→16.2s (cyclic<blocked-tree). 20/20 tests pass.
- ORE BATCH after inverse+loopback: +inverse(v6) MATCH=12 MISMATCH=0 OUT-OF-FRAG=13 TIMEOUT=8;
  +loopback(v7) MATCH=11-12 MISMATCH=0 (1017 non-inverse borderline ~26-40s flips w/ load,
  task #26). ZERO MISMATCH throughout all stages. Inverse-only onts now in-fragment: 10026
  (1774 subs), 10123 (11516 subs). Inverse+functional/symbolic still fenced (SHIQ needs M2
  ≤-rule). Net session: classifier now ALC+RBox+SH-transitive+SHI-inverse, exact vs HermiT.
- ORE batch FINAL (v4, all three changes): total=40 MATCH=7 MISMATCH=0 OUT-OF-FRAG=15
  TIMEOUT=11 CBERR=7(datatypes). The 7 MATCHes exact vs HermiT: 10056(1067 subs),
  10133(985), 10134(6794, SH transitive!), 10146(8813, SH transitive!), 10174(437),
  10176(106), 10199(1). Progression: pre-fix MATCH=5/MISMATCH=1/TO=20 → +RBox
  MATCH=4/MIS=0/OOF=21/TO=8 → +transitive OOF=15/TO=14 → +perf-pruning MATCH=7/TO=11.
  Two big SH transitive onts (10134/10146, ~7-9k subs) classified exactly = both
  transitive-un-fence AND perf-pruning validated together. Zero unsound.

PRIOR STATE 2026-06-06: M1 CORE DONE + tested. kobayashi-marust/engine/src/tableau.rs (new
module, mod added to main.rs): ALC fragment (concept/¬/⊓/⊔/∀/∃ + role hierarchy),
completion graph, Hyp-rule (Horn + disjunctive OR-branching with clone-on-branch DFS
backtracking), ∃-rule (runtime successor generation), clash, ancestor SUBSET blocking
(sound for ALC w/o inverse; root individuals not blockable so infinite ∃-chains
terminate after 2 levels). 7 unit tests pass (clash, sat, ∃+∀ clash/consistent,
disjunction both-branches-clash + one-open, infinite-chain termination); full suite
13/13. Hand-built clauses (solver decoupled from normalization). #![allow(dead_code)]
on the WIP module. NEXT (task #22): moose HT-clause emitter + JSON driver + validate
tableau terminates fast on stress/541 (where CB times out) vs HermiT. NOT yet wired to
CLI; standalone, no Lean yet (HermiT-validated when driver lands).
See [[project_km_reasoner_perf]] [[project_km_sroiq_program]] [[project_disjunctive_context_calculus]].
