---
name: project-km-10702-nomlink-fix
description: "2026-07-05 10702 wine incompleteness FIXED — nominal_clauses was missing the RoleAssertion half; nomlink clauses {a}⊑∃R.{b} close all 23; panel 48081439 validating"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05 (late): the last known incompleteness in KM's solved set (10702 wine,
23 missing `X ⊑ FrenchWine`) ROOT-CAUSED and FIXED.

**Root cause (frontend, not HT/CB):** `preprocess.rs nominal_clauses` has for
years augmented ABox **ClassAssertions** onto nominal proxies
(`C(a)` ⇒ `__nom__a(x) → C(x)`) but silently ignored **RoleAssertions**. So a
hasValue successor node carrying `__nom__BordeauxRegion` never received the
asserted `locatedIn(BordeauxRegion, FrenchRegion)` edge, and the (present and
correct) `__trans__locatedIn____nom__FrenchRegion` marker recognition had no
edge to fire on. Verified by clause dump: 0 clauses linked BordeauxRegion to
FrenchRegion. CB KM_NOMINALS (full DL7/DL8 Eq semantics) is complete here but
times out even at 320 s on this 1052-line ont (separate perf pathology).

**Fix:** in `nominal_clauses`, for each ABox `R(a,b)` where BOTH individuals
have nominal proxies, emit the pair
`__nom__a(x) → R(x, f_nomlink_a_R_b(x))` and
`__nom__a(x) → __nom__b(f_nomlink_a_R_b(x))` (deduped). This is `{a} ⊑ ∃R.{b}`,
entailed by the assertion under nominal semantics — interpreting each proxy as
exactly its singleton is the canonical extension in which every emitted proxy
clause holds, so the addition is UNCONDITIONALLY SOUND and purely additive
(more complete, never less sound). Byte-identical output for any ont without
nominal-proxied ABox role assertions.

**Result:** 10702: 564 → 587 subsumptions, GOLD-MATCH (0 miss / 0 extra), via
the production default route (no flags). 1375 tests green. Spot regression:
9540 (86 nominals, card route), 1603, 7499 all still MATCH on ws.

**Validation FINAL (panel 48081439): 574 gold-MATCH / 0 DIFF / 0 regressions;
10702 ok+MATCH.** First corpus table with ZERO incorrect results — everything
KM completes is sound AND complete; the 10 non-MATCH are all timeouts
(541 2669 3215 7914 9663 9724 10621 12653 14817 15516). COMMITTED f985b97. NB ws /tmp was wiped by a reboot
mid-session — a "timeout" on 9540 was a MISSING INPUT FILE (km reports worker
ofn exit 1 only on stderr); always check the ont file exists before reading a
timeout as a regression.

Related: [[project-km-card-default-on]] (the +3 card recoveries the same day),
[[project_km_nominals_cb]] (the full-Eq CB path this sidesteps).
