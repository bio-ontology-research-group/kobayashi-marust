---
name: project_km_nominals_routing
description: KM M2c full nominal reasoning (SHOQ tableau) + M3-lite engine router; CB blow-up is MEMORY not time; CB incomplete on inverse/nominal; domain/range CB fix
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Session 2026-06-08 (kobayashi-marust). Two deliverables, both validated vs HermiT,
0 MISMATCH. NOT committed (await user). Builds on [[project_km_hybrid_tableau]]
[[project_km_sroiq_program]] [[project_km_reasoner_perf]].

## M2c — full nominal reasoning (SHO/SHOQ), task #30 DONE
`engine/src/tableau.rs`: a nominal `{a}` is a singleton. Two additions, both reuse
the existing union-find merge (no new graph op):
- **o-rule** `apply_nominal_merges`, interleaved in `horn_saturate`: any two live
  nodes carrying the same `__nom__a` literal merge (deterministic, no branch).
  Merges happen PER disjunctive branch, so "at-most-one across branches" is free.
- **root seeding** in `find_model`: one non-blockable root per nominal (low id, so
  blockable nodes carrying `__nom__a` merge INTO it). Makes named individuals exist
  in every model -> ABox inconsistency (`{a}⊑C`,`{a}⊑¬C`) is caught.
Equality blocking switched on whenever nominals present (sound superset of subset).
NI-rule NOT needed for SHO/SHOQ (finite roots, merges only reduce); `cb_to_ht`
fences nominal+inverse `nominal+inverse(SHOI/SHOIQ)`. Converter now emits
`TInput.nominals` (was: fenced). Tableau `set_nominals`. ABox facts `C(a)` already
lifted by frontend to `__nom__a(x)->C(x)`.
Validated: 4 new Rust tests (16 tableau tests total pass), 6 `.ofn` fixtures
(`nom_singleton_unsat/_disjunction/_shoq/_abox_sub/_test/_inverse_fenced`) + HermiT
baselines in `oracle/results/`, all MATCH. ORE tableau batch unchanged (0 MISMATCH).

## M3-lite — automatic engine router `engine/py/route.py`, task #31 DONE
Picks CB vs hypertableau per ontology from one cheap parse. Two findings forced the
design:

1. **CB engine (owl_classify, clauses-only) completeness boundary** (measured vs
   HermiT): complete on EL/SH/SHQ + role hierarchy + transitivity + role chains.
   Was INCOMPLETE on domain/range (moose normalise does NOT fold them; Rust engine
   has no domain/range trigger — `A⊑∃r.B`,`domain(r)=D` did NOT give `A⊑D`). FIXED
   in `preprocess.domain_range_clauses` (called from `frontend.ofn_to_clauses`):
   backward Horn `r(x,y)->D(x)` / `r(x,y)->C(y)`, fires on Skolem edges, covers
   super-role via existing `r⊑s` clause. Pure input-clause augmentation -> engine
   calculus + Lean cert UNCHANGED. Still incomplete on **inverse** (engine never
   navigates inverse edges) and **nominals** (only ABox-grounded) -> route those to
   the tableau.
2. **CB blow-up is in MEMORY, not time.** `∀+⊔` can make CB materialise every
   successor-type combo; an `EquivalentClasses` stress hit **47 GB in seconds**,
   OOM-thrashing the host so a `subprocess` timeout could not fire. So NO
   try-CB-then-timeout race; decide up front + hard address-space cap on every CB
   call (default ~60% RAM). (Had to `kill -9` runaway CB procs from a prior session
   too — they ran 5h at 99% CPU.)

Routing (`live` = disjunctive clauses whose body concept is a successor concept,
i.e. asserted on a non-centre/Skolem term — the live `∀+⊔` pattern):
- in-frag + inverse|nominals -> tableau (CB incomplete).
- in-frag + live>0 -> tableau (CB could explode; never run it).
- else -> CB under the cap; on overflow fall back to tableau (in-frag) else
  `cb-failed` (never a wrong answer).

KEY EMPIRICAL RESULT: on ALL 40 ORE-sample ontologies `live=0` — every real CB
time-out is SIZE-bound (1012=1.8M clauses, 10248=67k concepts), NOT disjunction.
So the tableau is NOT their fix (it's slower, times out worse — 12 are
TABLEAU-TIMEOUT); CB scaling (semi-naive+parallel) is. This CORRECTS the old
[[project_km_reasoner_perf]] note calling 10248/10125/10161 "the tableau's job".
Also: the CURRENT CB engine (post semi-naive + audit) is far more robust to
disjunction than old M1 numbers — handles most synthetic `∀+⊔` in <1s; the routing
+ cap are the safety net for the adversarial residue.
Validation: router MATCHes HermiT on all 18 fixtures (without inverse/nominal
routing, 3 would be wrong) + 9 real ORE routed to CB (10056=1067 … 10146=8813 subs,
exact). Synthetic live-disjunction stress -> tableau, 0.1s, matches HermiT.

Files touched (uncommitted): `engine/src/tableau.rs`, `engine/py/cb_to_ht.py`,
`engine/py/preprocess.py`, `engine/py/frontend.py`, NEW `engine/py/route.py`,
`oracle/ontologies/nom_*.ofn` + `oracle/results/nom_*.json`, `docs/HYBRID-TABLEAU.md`.
