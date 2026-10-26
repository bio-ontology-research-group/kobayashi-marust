---
name: project_km_ht_search
description: KM HT disjunction-family gap traced to global ⊤-disjunctions branching on blocked nodes; modelprune net-negative on full corpus
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-17. HT (KM_HT, tableau_cli) search gap on the live-∀+⊔ family
(5303/10702/1603/...), traced via HermiT showboat traces + KM_HT_STATS.

**Root cause (definitive, from coredia diagnostic on 5303, committed 190fe53):**
HT models reach ~1000 nodes but **92–94% are already blocked** (anywhere-subset,
mode 1). Blocking is NOT the failure. The waste: `branch_pushes ≈ 22 ×
total_nodes_ever_created` (concept 1: 197 nodes → 4299 pushes; concept 9: 1163 →
47521). 5303 has 22 GLOBAL (⊤-headed, empty-body) disjunctions that fire AND
branch on EVERY node at creation, **including the ~93% about to be blocked**.
HermiT folds the same concepts to 3 nodes / 3–46 pushes (~1000×).

**KM_HT_EAGER (defer global disjunction FIRING to unblocked nodes) — REFUTED:**
model stayed 198 nodes, pushes 4318 ≈ baseline. Deferring firing didn't shrink
the model. Gated off, inert. Per-pass blocking already stops ∃-expansion at the
blocked frontier, so timing-of-firing wasn't the lever.

**KM_HT_BLOCKSKIP (the real lever, under validation):** suppress nondeterministic
BRANCHING on currently-blocked nodes (refresh blocked snapshot per branch
selection; skip any disjunction whose nodes are all blocked). Sound+complete for
the routable fragment: **ALC(H) has no inverse roles, so nothing propagates UP
from blocked successors** → skipping their branches/units can't change any
ancestor or root label; the unblocked blocker carries the same global
disjunction and detects any real clash. Expected: concept 9 ~47.5k pushes →
~22×(unblocked) ≈ 1.5k. Dev on /ibex/scratch/hohndor/km-incr (isolated engine
copy, never touches the running km/engine sweep binary). Validated by off-vs-on
output-IDENTITY gate (the soundness net) + 5303 finish/push-count. [[project_km_family_diagnosis]]

**KM_HT_MODELPRUNE (HermiT QuasiOrder multi-model pruning) — NET NEGATIVE, do
not promote.** Full-corpus panel (190fe53): ht-default 454 ok vs ht-modelprune
**447 (−7)**. Recovers 2 (10689,14216), regresses 9 into timeout — per-Phase-2-
test root_pos_label intersection overhead tips mid-size onts over the 240s wall,
load-sensitive. The earlier "27-ont sample +1 (464 vs 463)" was unrepresentative
+ within run-to-run timeout-boundary noise (ht-default itself drifts 463↔454).
Gated OFF, committed inert. Tables: results/benchmarks/2026-06-17-ht-fullcorpus-panel.md.

**RESOLVED via EMELIM (2026-06-17, HEAD 28597d4).** Root cause was UPSTREAM of
blocking: the clausifier emits complementary-definer pairs `⊤⊑A∨B` + `A⊓B⊑⊥`
(entails B≡¬A), forcing excluded-middle disjunctions that fire/branch on every
node (~23 Q_ definers bloat every label to size 24-40 vs HermiT 2-6). Fix =
substitute B:=¬A + drop the 2 tautologous clauses (model-preserving). Two gated
impls: KM_HT_EMELIM (cb_to_ht.py, literal polarity flip — HT format has neg) and
KM_EMELIM (frontend clauses.rs, moves atom across ⊑ — CB format positive).
- HT 5303: model 170→7 nodes EXACTLY = HermiT, branch_pushes 3718→0, timeout→0.083s.
  HT panel: 454→465 ok / 453→459 MATCH (+14, recovers disjunction family). 3
  "unsound" all gold artifacts (15516/2669 stale SWRL gold; 10908 pre-existing
  HT-engine breakage exposed by finishing — incomplete=5918+3spurious; HermiT
  says consistent). EMELIM 30/30 identity-clean where off/on both finish.
- CB sweep 587 (km-incr base): 555→557 ok GOLD-CLEAN (0 unsound/0 incomplete),
  recovers 16444 (CB memout) + 6212, mem 930→865 MB, 0 regressions. Does NOT fix
  the disjunctive-saturation family in CB (5303 still timeout, but mem halved).
Tables: results/benchmarks/2026-06-17-emelim.md. Both gated default-off — candidate
to enable (CB strict win; HT via routing). KM_HT_BLOCKSKIP refuted (sound but slower).

**Soundness invariant: unsound=0 across ALL HT arms.** Only HT incompleteness =
ont 7216 (48962 missing subs, disj=0/trans=0 — large near-Horn taxonomy gap, NOT
the disjunction family). docs/ht-search-debug.md has the full lever-elimination
trail.
