---
name: project-km-card-default-on
description: "2026-07-05 card+recog flipped default-on (panel-clean +3); 541 solved by KM_HT_CARD_FN functional→≤1 tagging; 7499 \"incompleteness\" = gold localname collision"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05 (evening): closing the 13 ORE timeouts via flags + card work.

**KM_HT_CARD + KM_HT_CARD_RECOG flipped DEFAULT-ON** (opt-out `KM_NO_HT_CARD` /
`KM_NO_HT_CARD_RECOG`, matching the KM_NO_HT_SHOQ pattern). Validation = full
584-ont km-only card panel (IBEX job 48067625): 574 ok, **573 gold-MATCH, 1
DIFF (10702 pre-existing), 0 MATCH→DIFF regressions**, recovers **1603 (21.7s),
9540 (20.8s), 7499 (82.5s)**. Flip sites: orchestrate/config.rs, race.rs (x2),
cb_to_ht.rs drop_em, frontend/normalise.rs Clausifier.card, bin/km.rs,
hypertableau.rs Ht init. `KM_HT_RULES` kept OPT-IN (not in panel; also disables
emelim globally via `!ht_rules` in cb_to_ht:2112). 1375 tests green; 1603
re-verified MATCH with NO env on ws.

**7499 was NEVER incomplete** — the raw-JSON "3297 missing" vs gold is a
localname collision: ont has ONE axiom in `purl.org/obo/owl/CHEBI#` namespace
(`PRO#PRO_000000001 ⊑ CHEBI#CHEBI_23367`, orphan leaf) while the BFO hierarchy
is in `purl.obolibrary.org/obo/CHEBI_...`; no bridging axiom. Konclude gold
bridges them only through localname canonicalisation; the harness ore_canon
closure makes KM MATCH. Same artifact class as 12698's residual 18.
[[project-km-12698-named-fix]]

**Added `transitive_close_subs` at the HT serialization boundary**
(tableau.rs run_json, both Ht and legacy-Tableau paths; helper pub in
hypertableau.rs). Sound (only adds entailed pairs). Phase-2 misses A⊑C when
A⊑B⊑C and C is an inferred (non-told, e.g. domain/range) subsumer absent from
A's one captured model label. Benchmark-inert (ore_canon already closes) but
correct-by-itself output for API consumers.

**541 recovers with `KM_HT_CARD_FN=1` but the flag is NET-NEGATIVE globally —
STAYS OPT-IN, do NOT promote.** (opt-in, frontend/normalise.rs): tags
`FunctionalObjectProperty(R)` as first-class `⊤ ⊑ ≤1 R.⊤` — fresh universal
marker `Q_fn_<role>` asserted as ⊤-fact, CardMeta{marker=filler=Q_fn, max, n=1}.
Raw Eq clause kept (CB consumes; redundant-sound on HT). cb_to_ht card_drop
can't mis-fire (Eq clause body has no concept atom; ⊤⊑Q_fn head len 1 < EM
min 2). 541: timeout-in-all-12-flag-configs → 21s GOLD-MATCH. BUT the cardfn
corpus panel (48080229) FINAL: 572 MATCH vs 573 default = **NET −1**. Two
STABLE regressions: **1016 MATCH→DIFF** (correctness break on 1016's functional
roles) and **7581 MATCH→timeout** (extra markers + emelim-disable over budget;
7581 was a hard-won INVCHAIN+GFCERT recovery). vs only 541 recovered. (Mid-run
9635/9674/14042/6246 flickered = timeout-boundary flakiness, settled back to
MATCH.) The
functional→≤1 tagging that solves 541 is unsound/too-costly on other
functional-role onts; making it safe would need selective routing (structural,
not per-ont). So 541 is NOT cleanly recoverable; KM_HT_CARD_FN kept gated OFF.

**Flag sweep verdict (156 pairs, job 48066078)**: 1603/9540=card,
15516/2669=rules (0.06/0.11s, HermiT-correct contested gold), all other
timeouts (10621 12653 14817 3215 541 7914 9663 9724 7499) = NO flag config
helps (7499's card "NEAR" rows were the collision artifact).

**Residual 9 timeouts (need code)**: 9724/7914 SRIQ number (HT unsound:
shared-filler ∀), 10621/12653 datatype cardinality (no concrete-domain oracle
in HT), 14817 role chains, 3215 big disjunctive, 9663 CB 115GB blowup, 541
(pending cardfn validation), rules pair (contested gold, opt-in works).

**Uncommitted-tree caveat**: working tree carries ~2600 lines of konclude_ht/HT
WIP (hypertableau +1626, cb_to_ht +607, tableau +417 beyond fmt) predating this
session; all panels/tests validate the BUNDLE. Card default flips are
interleaved in the same files. Commit strategy pending user input (asked; user
said "continue" = keep working). Deployed to IBEX via rsync (source of truth
for panels).
