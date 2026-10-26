---
name: project_km_disjunction_blowup
description: "Profiling of the ORE disjunction-timeout class (10702 etc.): incomparable disjunctive-fact blowup; the fix is ordered resolution, not more subsumption"
metadata:
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-10. Profiled the remaining CB-engine disjunction timeouts with the
current engine (central+sharing+subsumption-redundancy all in place). Used a
KM_TRACE head-size histogram (committed `c4cbb59`).

**ore_ont_10702 (el_rbox_safe=False, CB-routed) — the representative case.**
worked_off grows linearly without converging: 297k -> 1.16M clauses at 120s,
`max_body_len=0` (pure disjunctive FACTS `⊤ -> disjunction`). Head-size
histogram at guard 1M (central, 1 thread): `head[<=1=17856 2=321657 3=616084
>=4=40077]`, max_head_len=6. The **3-literal disjunctions grow fastest**
(203k->313k->453k->616k) while 2-literal plateaus. These are INCOMPARABLE
disjunctions (`{A,B}, {A,C}, {B,C}, ...` with no subset relation), so
forward/backward subsumption (already implemented: `fwd_subsumed`, back-subsume,
head-literal subsumption index, Elim rule) CANNOT prune them. contexts=1607.

Legacy (KM_NO_CENTRAL): contexts=240, `head[<=1=31260 2=403436 3=14827
>=4=40125]`, max_body_len=2 (hypotheses p->p). So central EXPLODES the 3-literal
class (616k vs legacy 14.8k) for this ont, but BOTH strategies time out
(legacy: 489k worked_off at guard 400k, still growing). So the central->legacy
fallback can't rescue 10702. 1603 and 9540 also time out under BOTH strategies.

**Conclusion: the lever is ORDERED RESOLUTION (Sequoia), not more redundancy.**
Subsumption is maxed out; it can't touch incomparable disjunctions. Sequoia
imposes a total order ≻ on literals and only resolves the ≻-maximal literal of
each clause, cutting the combinatorial generation at the source. This is a
MAJOR engine change (the Hyper rule must respect a literal ordering) AND needs
Lean re-certification (it changes "what gets derived" = CB-calculus logic; see
CLAUDE.md re-cert rule). This is the deferred "hard part" CLAUDE.md names.
Scoped next step for beating Konclude/ELK on the ~8-10 disjunction timeouts.

**Full non-ok categorization (28 onts, sweep 5518 + profiling jobs 5557/5585).**
The gap to Konclude (587) is 25 onts spanning FOUR distinct hard problems, not
one:
- **Disjunctive blowup, CB** (incomparable 2-3 lit disjunctions; ordered
  resolution + subsumption already maxed): 10702, 9540, 1603, 10860, 5303.
- **Context explosion** (tens of thousands of contexts; central keys a context
  per trigger-set core): 6682 (129530 ctx!), 7127 (79k), 7914 (21k), 7499
  (8.4k), 11311 (15.6k, HITS the 5M msg cap -> truncated/incomplete, exit 0).
- **Giants** (2.5-3.1M clauses): 8737, 16744 -- see [[project_km_giant_routing]].
- **Large/slow** (huge clause files, <200k guard in 60s): 1194 (253MB), 7246
  (152MB), 7581 (107MB), 4669 (103MB), 9663 (63MB), 14817 (55MB), 16444 (45MB),
  4205/6212/15703/15803 (elc-exit-3 then CB on 70-300MB files).
- **elc-exit-3** (el_rbox_safe=True but TBox non-EL -> elc bails -> CB): 3215,
  4205, 4604, 5303, 6212, 6682, 11460, 15491, 15703, 15803. (Overlaps the above
  by CB behaviour.)
- **Borderline-flaky** (parallel-nondeterminism at mem boundary): 11311, 11745,
  6682, 7127.

**KM already implements ordered resolution** (Hyper fires only on ordering-
maximal head literals, engine.rs:731; ordering total on same-term concepts by
iri, calc.rs:407) AND subsumption-redundancy. So the disjunctive blowups are
genuine hard instances, not a missing-feature gap. Matching Konclude (a mature
optimised reasoner) on all 25 is multi-session reasoner research, not a single
fix. Realistic levers, by tractability: (1) context-explosion -> strategy
routing/racing central-vs-per-f (testing whether per-f converges where central
explodes); (2) giants -> concept-relevance; (3) disjunctive blowup -> deeper
ordering/redundancy (research). NO unsound shortcut is acceptable (CLAUDE.md:
fully sound + complete competitor).

**2026-06-11 update — the exact ordering mechanism + why routing can't fix it.**
Confirmed root cause in code: `calc.rs pred_lteq` ROOT branch keeps named query
concepts on the central term MUTUALLY INCOMPARABLE, because the subsumption
readout (`engine.rs subsumptions()`) reads units `-> B(x)` from the context
cored at A and needs every named concept exposed. That incomparability disables
ordered resolution AMONG named concepts, so a disjunction of named concepts has
ALL head literals maximal -> Hyper resolves on each -> the incomparable 2-3 lit
disjunctions explode. Pure-legacy with the FULL 240s budget (job 5655) times out
on ALL 7 (10702 9540 1603 10860 5303 10621 9663), so the central->legacy
fallback / strategy routing CANNOT rescue them. The EL certificate
([[project_km_el_certificate]]) also can't (covering disjunctions aren't
model-satisfied). The ONLY fix is the Sequoia scheme: total order even among
named concepts, readout completeness recovered via the context CORE not
maximality. That changes WHAT is derived (calculus logic, encoded in
lean/CompletenessStrategy.lean) -> a wrong order silently breaks completeness
across the WHOLE sweep -> needs the careful rewrite + Lean re-cert (task #10),
NOT a same-session edit. This is the documented hard part.

**2026-06-14 — IBEX diagnostic FALSIFIES the "ordered resolution is the fix"
hypothesis (jobs 47512776 5303, 47513254 10702, absorbed clauses, on `ssh dragon`
[[project_km_ibex_env]]).** Ran base vs KM_SEQ_ORDER vs KM_ORDERED_ALL with long
(360-600s) budgets unimatrix's 240s cap never allowed:
- **10702** (the memory-blowup representative): KM_ORDERED_ALL (TOTAL order) does
  NOT bound the population — worked_off 304k->505k->**2.13M still growing**, RSS
  4.0GB at timeout, with the **3-literal disjunctions exploding even ordered**
  (head[3]: 113k->248k->**1.45M**). base stayed <200k/51MB (slow churn, no
  progress, also timeout). So a total order does NOT tame the covering-disjunction
  product, because the disjunctions are body-empty FACTS (⊤->A∨B∨C): resolving the
  ordering-maximal disjunct yields another SAME-WIDTH 3-lit disjunction, so the
  product is never cut. **Direction A (ordered resolution + residue readout, task
  #25) would NOT solve this family** — refuted by measurement, not just net-neutral.
- **5303**: base timeout/73MB, KM_ORDERED_ALL timeout/415MB (bounded mem, still
  no converge in 600s), KM_SEQ_ORDER **OOM 25GB** (actively harmful). 5303 is a
  slow-SEARCH case (bounded population, deep search), not a population blowup.
- **CONCLUSION / PIVOT**: the live-disjunction family needs CASE-SPLITTING /
  tableau (Direction B/C [[project_km_disjunction_split]]) — splitting REMOVES the
  disjunction (assume one disjunct) so the product is never materialised, exactly
  what ordered resolution fails to do here. The residual lever is Direction B/C
  search CONVERGENCE (the cache tableau oscillates on 5303/1603/12141), NOT ordered
  resolution. Deprioritise task #25 (Direction A); focus the residual on Dir B/C
  convergence + routing the cache tableau into owl_classify. NB KM_SEQ_ORDER is not
  merely net-neutral — it OOMs 5303 — so it must never be defaulted on.

Related: [[project_km_central_strategy]], [[project_km_giant_routing]], [[project_km_el_certificate]], [[project_km_disjunction_split]], [[project_km_ibex_env]].
