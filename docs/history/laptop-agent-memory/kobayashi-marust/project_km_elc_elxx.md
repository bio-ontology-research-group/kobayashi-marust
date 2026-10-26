---
name: project_km_elc_elxx
description: "2026-06-22 ELK-guided EL++ completion of elc: reflexive roles (committed bf40744, validated 0/0) + native domain/range (in A/B). Cloned liveontologies/elk-reasoner, ported its reflexive/range semantics. elc was already ELK-style + had a residual certificate; the real gaps were reflexive-role ROUTING and domain/range being cert-only (bailed to CB)."
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

User directive (2026-06-22): clone ELK (github.com/liveontologies/elk-reasoner),
study its code, then "complete the elc with all EL++ features and the
optimizations used in ELK." Cloned to /tmp/elk-reasoner; two Explore agents mapped
(a) its inference rules / EL++ coverage and (b) its saturation optimizations.

## What elc already had (do not re-port)
NF1-NF7 (incl. role chains/transitivity as NF7, role-hierarchy closure), ⊥-edge
propagation, clone-free in_edges, FxHash-indexed rules, AND a residual-certificate
path (cert_round/check_certificate/repair_certify) that checks non-EL clauses
(disjunctions/nominals/cardinality) against the canonical model. So elc is already
ELK-style and already a sound+complete EL++ *router* (non-EL -> cert or CB).

## ELK findings (key ones)
- ELK normalizes Reflexive(R) -> ⊤⊑∃R.Self -> IndexedObjectHasSelf decomposition =
  self-loop link (C,R,C) at every context + C⊑D for each range D of R. ELK marks
  reflexive+chain only PARTIALLY supported.
- Ranges via RangeFiller / SubClassInclusionRange (filler of ∃R.x becomes x⊓range).
- Optimizations: rules compiled onto indexed expressions (elc already indexes by
  concept); role-partitioned backward links (in_edges by role); dual composed/
  decomposed subsumer store; ArrayHashSet small-set repr; active-context tracking.
  These are PERF-only; elc is already fast on ORE (lattice median 0.27s) so payoff
  is marginal there. Not yet ported.

## Landed
1. **Reflexive roles (COMMITTED bf40744)** -- the real gap: frontend already emits
   `[]->R(x,x)` (normalise.rs:812) but to_nf dumped it to residual and rbox.rs
   FENCED "reflexivity" so el_rbox_safe=False -> whole ont went to CB. Fix:
   to_nf parses it into `reflexive_roles`; build_idx closes up the role hierarchy
   (R(x,x)∧R⊑S⟹S(x,x)); classify_inner seeds self-edge (C,R,C) at every concept
   node; existing NF4/NF7(both positions)/⊥-edge/role-lift fire through the normal
   fixpoint -- self-edge in NF7 both directions also CLOSES the reflexive+chain
   corner ELK leaves partial. rbox.rs split: Reflexive=EL-safe (admitted by
   el_rbox_safe + el_rbox_safe_relaxed), Irreflexive (R(x,x)->⊥) stays fenced.
   Validated: +2 unit tests; full sweep 47709413 = 0 unsound / 0 incomplete; the
   13 corpus reflexive onts -> 4 newly route to elc (10326/13078 unscored extras;
   8298/869 SCORED, gold-clean BYTE-IDENTICAL 12200/12200 & 12224/12224, ~0.25s on
   elc vs CB). Coverage unchanged (reflexive can't reduce it); the 18 fails in the
   sweep are exactly the known-unsolved-18, +3 contention victims (6212/10908/15491
   = absorb recoveries that timeout under IBEX load, pass on clean nodes).

## Tried + REVERTED
2. **Native domain + range (REVERTED -- caused incompleteness).** Implemented
   domain=NF4(filler ⊤) + range=nf_range fired in Edge rule. Unit tests passed,
   114/114, but the A/B sweep (47709485) showed INCOMPLETE on 1618(3)/2860(134)/
   3260(66). Root cause: native domain/range only fires on EL (NF3) edges; when the
   triggering existential edge lives in the RESIDUAL (non-EL ont, el_rbox_safe=
   False -> certified-elc portfolio via race_adaptive_vs_elc / KM_ELC_CERT=2), the
   consequence (e.g. Light⊑Sensor from domain(has_reading)=Sensor) is missed, AND
   removing domain/range from residual stops them marking the concept "unresolved"
   (which would route it to the engine). So elc emits the concept RESOLVED with an
   incomplete super-set. CONCLUSION: elc ALREADY supports domain/range soundly+
   completely via the residual certificate; native handling is a real completeness
   problem (residual-edge interaction) not worth marginal speed. Reverted
   elcomplete.rs to bf40744 (git checkout HEAD; all dr edits were confined there;
   rbox.rs/CHANGELOG untouched by it). LESSON: the certified-elc portfolio runs elc
   on el_rbox_safe=False onts too, so an elc change can regress CB-routed onts.

## Env gotchas (this session)
- ws-built binaries DON'T run on IBEX (GLIBC 2.39) -> MUST build on IBEX
  (/ibex/scratch/hohndor/km/engine, ~/.cargo/bin/cargo, ~70s).
- `ofn <ont.ofn> --meta <metafile>` (ont is a PATH arg, clauses to stdout; NOT
  stdin). el_rbox_safe is in the meta JSON.
- IBEX corpus = /ibex/scratch/hohndor/km/corpus (587 = scored_onts.txt; some extra
  .owl like 10326/13078 are UNSCORED, no gold). Gold = gold/konclude__*.sig.gz.
- Reuse feat_ablate.sbatch with `--array=0-29` to run ONLY the base arm (ID/30=0)
  over the full corpus = single-arm regression sweep. Results abl_res/base__c*.jsonl,
  per-ont gold cmp via sig_cmp.py (cmp_unsound/cmp_incomplete keys).

3. **NF4 filler-label indexing (COMMITTED f0331bb)** -- the ELK perf optimization.
   Profiled elc on 8737 (slowest EL ont): pure NF4, Edge rule scanned 8.6B
   (super_role,d_super) probes = full sub_super[d] label per edge; Sub rule 1.68B;
   NF2/NF7 zero. perf NOT on cluster -> added gated KM_ELC_PROFILE per-rule scan
   counters. Fix (only existential FILLERS fire NF4, ELK-style): Edge rule scans
   nf4_label[d] = maintained NF4-filler subset of sub_super[d] (is_filler set at
   init, appended in add_sub) -> 8.64B->4.33B; Sub rule gated on d being a filler
   (nf4_by_filler) -> 1.68B->505M. BYTE-IDENTICAL (113 tests, same 409836 subjects,
   full sweep 47709731 = 0 unsound/0 incomplete). **8737 classify 84->63s; pipeline
   130->67s (-49%); 16744 65->48s (-27%).** GOTCHA: first tried iterating NF4 axioms
   per edge (nf4_by_role) -> SLOWER (8737 has many NF4 axioms per role, ran >10min)
   -> discarded. The filler-label subset is ⊆ sub_super[d] so never worse.
   Profile method: ofn ont.owl --meta meta > $KM/8737.clauses (cache in scratch);
   KM_ELC_TIMING=1 KM_ELC_PROFILE=1 elc < clauses.

## Landed (cont.)
4. **ELK backward-link PROPAGATION + parse-tree discard (COMMITTED 387b511)** --
   the core ELK saturation optimisation (Incredible ELK §5). Explore-mapped the
   ELK Java (ContextImpl, SubsumerBackwardLinkRule, SubsumerPropagationRule,
   PropagationFromExistentialFillerRule). TIME: Edge-NF4 still rescanned
   role_supers(r)xnf4_label[d] per edge = 4.33B hashmap PROBES (mostly missing).
   Replaced with a per-context propagation store `prop[(d,r)] = {E: ∃r.X⊑E,
   X∈label[d]}` keyed by the EXACT edge role (role hierarchy handled by the
   pre-existing edge-LIFT, which already materialises every super-role edge as its
   own worklist item -- so exact-role keying needs no role-closure scan). New edge
   (c,r,d) fires prop[(d,r)] in ONE lookup; new filler-subsumer at c registers
   into prop[(c,·)] + fires existing exact-role backward links. Each (link,prop)
   pair fires once = ELK's join. Edge lookups 4.33B->23M. **8737 classify 63->22.4s.**
   Removed the old (role,filler)->[sup] index. Propagation-Set dedup (ELK uses a
   Set) MEASURED USELESS (<0.5% bucket dup on 8737, contains-check added cost) ->
   reverted, kept Vec. MEM: elc held the full input (millions of String-owning
   JClause) alive through saturation via the &[JClause] borrow. classify now takes
   clauses BY VALUE and drop()s them right after to_nf (which already interned EL
   into nfs + cloned residual), before saturation. **8737 peak 9.7->5.5GB (-43%)**;
   the explicit dealloc adds ~4s on giants (OS would reclaim at exit) but they're
   far under 240s + the memcap headroom matters. Only 1 prod caller (cli.rs:173)
   + classify_inner tests (now by-value, clone where reused). 113 tests pass;
   8737+16744 gold-clean 0/0. Full regress sweep 47711101 (base arm, full corpus)
   in flight.

## ELK/Konclude head-to-head + routing recovery (2026-06-22, COMMITTED 314bec5)
Reasoners on IBEX: Konclude=/ibex/scratch/hohndor/km/bench/reasoners/Konclude-v0.7.0-1138-.../Konclude;
elk.jar=.../elk-distribution-cli-0.6.0/elk.jar; hermit jar in km/bench/hermit_cp.
PRIOR run data (wall+peak_mb+match) already in /ibex/scratch/hohndor/km-incr/bigsweep/
results.jsonl (runners: konclude/elk/km-base/...). MINE that, don't re-run.
KEY FINDINGS:
- **On pure-EL giants KM now BEATS ELK memory**: 8737 ELK=16.4GB(JVM!)/50s,
  Konclude=7.1GB/42s, KM(new elc)=**5.5GB/22s**. The "ELK uses less mem" premise
  is FALSE on big EL onts -- the parse-tree discard put us ahead.
- Our 22 timeout/memout: ELK produces a sig for ALL 22, but ELK is EL-ONLY so for
  non-EL onts it DROPS the non-EL axioms and returns an INCOMPLETE approximation.
  Split by ELK-vs-gold MATCH: only **8 ELK-correct** (15803,1603,12653,6934,16444,
  6212,7581,10908); **14 ELK-approximates** (wrong, genuinely need CB/HT).
- Of the 8 ELK-correct: **15803+6212 are el_rbox_safe=True >100MB GIANTS** -> the
  elc-portfolio is SUPPRESSED for giants (concurrent CB+elc OOMs >100MB) -> they
  fell to BARE elc (cert OFF, mod.rs:206) -> bailed on residual -> CB -> 18GB/240s
  timeout. FIX (314bec5): bare-elc bail on an EL-safe giant now RETRIES elc with
  KM_ELC_CERT=2 (repair cert), bounded by elc_force budget (100s/14GB), before CB.
  The repair cert certifies the inert covering disjunction (= what ELK computes).
  RECOVERS 15803 (240s->20.7s/1.26GB) + 6212 (->76.8s/1.24GB), gold-clean.
  **565 -> 567 ok.** Pure-EL giants (8737/16744, no residual) untouched (solve on
  1st attempt). Sequential retry = no concurrent-race OOM. Full sweep 47711943
  FINAL: **568 ok / 17 timeout / 2 memout, gold_match=568, 0 unsound / 0 incomplete,
  0 regressions** (recovered = 15803, 6212 [my change] + 15491 [a prior memout =
  IBEX-load contention victim, el_rbox_safe=False/CB-bound, recovered on a clean
  node -- may flip back; durable = +2]). CI was RED on ALL commits (pre-existing):
  Cargo.lock missing the libc edge (libc added to Cargo.toml, lock not refreshed)
  -> `cargo build --locked` refused. Fixed (1e97904, +1 line), CI now GREEN. NB ws
  builds WITHOUT --locked so it auto-fixed its lock + hid this; reproduce --locked
  on ws to catch it.
- The other 6 ELK-correct (1603/12653/6934/10908/16444/7581) are el_rbox_safe=FALSE:
  elc-cert exits 3 (uncheckable residual shape = nominals/inverse, or saturates
  then fails). NOT elc-recoverable as-is -> would need cert to handle those shapes
  (future). They stay CB/HT-bound.
- elc_portfolio default ON (KM_NO_ELC_PORTFOLIO to disable); so the bare-elc path
  (mod.rs:204 `el_rbox_safe && !portfolio_on`) is hit ONLY for >100MB giants.

## Assessed + NOT done (remaining ELK opts -- marginal/risky for elc)
- ArrayHashSet small-set subsumers: helps SMALL sets; giants have LARGE sets
  (4.06B add_subs = large fan-in) where FxHashSet wins; sub_super is THE central
  cloned structure -> high regression risk on 565-clean baseline. Median already
  ~0.27s. Skipped.
- Role-partitioned in_edges (ELK SubContext-per-role): the NF4 sub-side
  (nf4_sub_scan 600M) is already cheap vs edge-side 4B; flat in_edges needed for
  ⊥-backprop + NF7. Marginal. Skipped.
- Dual composed/decomposed subsumer store: N/A -- elc never stores existentials
  as subsumers (uses edges directly).
- VERDICT: the high-value ELK saturation opt (backward-link propagation) is in;
  the rest don't help elc's profile or are too risky. Giants still NOT unlocked by
  EL++ alone (7246 symmetric, 7581 inverse, 15803 disjunction) -- see
  [[project_km_ablation_router]].
- HEAD = 387b511 (reflexive bf40744 + filler-label f0331bb + this). NOT pushed.
