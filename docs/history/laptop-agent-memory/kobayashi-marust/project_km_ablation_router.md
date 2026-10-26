---
name: project_km_ablation_router
description: "2026-06-21 full-corpus feature ablation: KM_ABSORB_PORTFOLIO is the sole +4 lever (promoted default-on); per-ont lattice = 4.7x median memory via structural router; the throughput GIANTS are near-EL blocked by reflexive/symmetric roles, NOT research-grade Horn-SHIQ"
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

User-directed campaign (2026-06-21): full ORE ablation, every feature ON
individually, measure time/mem/sound/complete, find levers, combine, derive best
config PER ONTOLOGY, generalize. All on IBEX (`ssh dragon`, pi-hohndor, batch).
Harness in `results/ablation/` (feat_ablate{,_r2,_r3}.sbatch, lattice.sbatch,
probe18.sbatch, sig_cmp.py, ablate_agg.py, per_ont_best.py, feat_extract.py,
clause_profile.py). Snapshots in `results/benchmarks/2026-06-21-ablation/`.

## Coverage (rounds 1-3, 44+ configs)
- base (all-default) = 565 gold-clean. **KM_ABSORB_PORTFOLIO is the ONLY lever
  that moves coverage: +4 (6212/10908/15491/16444) = 569, 0 unsound/incomplete/
  regress, and it subsumes EVERY recovery any single flag OR combination gives.**
  PROMOTED default-on (commit: config.rs absorb_portfolio/absorb_on default true,
  opt-out KM_NO_ABSORB_PORTFOLIO).
- Flag-space ceiling = 569/587. The 18 unsolved are flag-INVARIANT: identical
  across all 44 configs AND probe18 (10 aggressive combos @ 600s/40GB) recovered
  ZERO, none even ok-but-incomplete. They are algorithm/scale-bound, not config.
- 18 split structurally: 2 SWRL contested-gold (2669/15516, unreachable by
  design -> real target 585); 6 disjunction-family-with-inverse/nominal/card
  (1603/6934/9540/12653/15672/10702, HT-unsound so CB-only); ~10 large
  memory/throughput.

## Per-ont time/mem (lattice = 14-config factorial, ont-major, clean within-ont)
- Median peak 108->23 MB (**4.7x**), median wall 0.46->0.27s, aggregate 486->248
  GB-s, ALL coverage-preserving. 230 onts have >80MB & >25% headroom (several GB).
- Generalization (one feature dominates): **d_nonEL≈0 (pure-EL-clause) -> run
  lean = noelc + threads=1 (+ often noabsorb/nocentral)**. The big levers are
  elc-portfolio + central + THREADS (threads amplifies memory; was never varied
  before). HT racer is a minor tax. Feature-rich onts (disjunction/inverse, the
  10-ont full16 group) keep full machinery. central needed for a small set
  (1016/11623/11745/6682/7127/7956/9944). => structural router, not a global flip.

## BREAKTHROUGH: the throughput giants are NEAR-EL, not Horn-SHIQ-hard
clause_profile.py on the giants (overturns project_km_throughput "research-grade"):
- **7246: 100% EL normal forms (NF1/NF3/NF4), ZERO non-EL clauses.** elc exits 3
  only because el_rbox_safe=False from RBox: 55 transitive (FINE, folded to NF7),
  9 symmetric, **6 reflexive**. el_rbox_safe_relaxed admits inert symmetric/inverse
  but had NO reflexivity arm -> reflexive roles block unconditionally.
- 15803: 99.997% EL (16 disjunctions w/ __nom__ nominals + 9 many-body); el_rbox
  _safe=True but bare-elc exits 3 on the 16 disjunctions; cert says 15% concepts
  insufficient.
- 7581: 99.99% EL (32 many-body + 1 role-chain-ish OTHER); inverse+chains.
=> Recovering them = EXTEND elc with the EL++ features it omits (reflexive,
symmetric, then disjunction/nominal residue), NOT a new calculus. elc is already
ELK-style (FxHash, indexed NF1-7, clone-free in_edges; elcomplete.rs run() loop).

## Landed / tried
- absorb default-on: COMMITTED + validated (spot-check: default path recovers
  15491/9024/5303/12141 clean; 6212/16444 clean on compute nodes, login-contention
  only).
- Rc<ContextClause> arena (kill saturate per-iter deep clone, engine.rs:1351):
  built + 111 tests pass, but A/B showed ~0 speedup on CB onts (9944/12698) ->
  the clone is NOT a bottleneck (per-context cost dominates). REVERTED.
- IN FLIGHT: reflexivity-inert arm in el_rbox_safe_relaxed (rbox.rs) to route
  7246 to elc when its reflexive/symmetric roles are inert. Sound iff !relevant
  (same guarantee as symmetric/inverse). Testing whether 7246's roles are inert.
NEXT if 7246 routes+gold-clean: a giant recovered by a sound 1-line routing fix.
Else: implement reflexive self-edges in elc (materialize for declared reflexive
roles; complete; needs byte-identical-gold validation before trust).
