---
name: project-km-speed-polling
description: 2026-07-05 speed work — adaptive subprocess polling (f05bccd) removed the ~0.2s small-ont latency floor; race-mode measured unsafe as default
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05 speed dimension of the beat-Konclude goal.

**Adaptive polling LANDED (commit f05bccd, payg-strategy).** Every orchestrator
subprocess wait polled at a fixed quantum (100ms run_engine RSS/wall watchdog;
200ms tableau grace delay; 50-100ms race loops), so a worker exiting in ~10ms
was noticed only at the next quantum → each pipeline stage had a ~0.1-0.2s
latency floor. On small onts THAT was the wall (ore_ont_105: engine 0.01s, ofn
0.00s, km classify 0.19s). Replaced every fixed sleep with 1ms-doubling-to-old-
quantum backoff. Result-identical (12698/10908/15672/10702 unchanged).
105 classify 0.19s → 0.05-0.06s (3.5x). Konclude median on the 425 sub-second
ORE onts is 0.20s, so this puts KM's fixed cost below it. Fresh panel measuring
WIN-count lift: BUILD 48062296 PANEL 48062298.

**Race mode (KM_HT_MODE=race) MEASURED UNSAFE as default (sweep 48060733,
584 onts on the post-named-fix binary):** 2 gold MATCH→DIFF regressions —
7216 (Horn taxonomy, HT returned a PARTIAL 43682/92644 that race accepted) and
7901 (+2 extra/-1 = unsound); 0 recoveries; median speedup only 1.02x. Keep
KM_HT_MODE=fallback default. BUT race cuts the 225s HT-budget-pinned onts
hugely: 9635 225→0.5s, 9024 225→0.9s, 12141 225→1.1s, 5303 225→8.9s,
15491 225→16.6s (these are disjunction-family/central-blowup where CB is doomed
and fallback waits the full KM_HT_BUDGET_S=225s before taking HT).

**Why race is unsafe — two masked HT bugs (both diagnosed 2026-07-05, both
hidden because CB wins these in fallback):**
- 7216 (Horn taxonomy): HT INCOMPLETE — worker returns 62274 subs, already
  transitively closed (closing it stays 62274), vs gold 92644. ~30k genuinely
  un-derived. Not a cap/partial; a real HT algorithm gap on large Horn
  taxonomies. So a TOutput "complete" flag based on "no cap hit" would falsely
  mark it complete → complete-flag lever does NOT rescue race.
- 7901 (has DATATYPES): HT UNSOUND — wrongly derives ChemicalStructure and
  DrugTreament ⊑ ⊥. Root cause: 7901 has `DataExactCardinality(1 structureData)`
  etc.; these datatype cardinalities were NOT fenced (TInput number=true,
  fenced=0) so HT reasoned structureData as an object role and clashed a
  satisfiable concept. The has_datatype/fence guard missed DataExactCardinality.
  LATENT SOUNDNESS RISK: if a datatype ont ever CB-times-out and HT fills it in
  fallback, the answer would be wrong. Masked now only because CB wins.
  NB `ht_routable` (race.rs) does NOT check datatypes (only fenced/dropped/
  nominals/inverse), which is how 7901 reached HT. TRIED adding a
  `tin.concepts.any(__dt__)` fence there and REVERTED: 9635 is a datatype ont
  HT currently rescues CORRECTLY (gold-MATCH; its datatypes are benign
  DataHasValue/DataOneOf, no cardinality clash), so the blanket fence turns
  9635 ok→timeout — a regression with no fallback-correctness gain (fallback is
  already sound). A PRECISE fence (only DataMin/Max/ExactCardinality) would
  protect 7901 without touching 9635, but it's race-mode-only value; deferred.

**Safe lever for the 225s-pinned family (TODO):** TOutput (race.rs:29,
tableau.rs:4903) has NO complete/capped flag. Add one (HT sets complete=true
only when classification reached fixpoint without hitting any node/time cap),
then in fallback accept HT's answer as soon as it's ready IF flagged complete —
7216's partial gets rejected (CB wins) while the CB-doomed onts get HT's
complete answer immediately. Lowering KM_HT_BUDGET_S globally is UNSAFE (breaks
slow-but-correct-CB onts like 7216). Even so, the disjunction family (5303 etc.)
stays seconds-to-minutes where Konclude is <1s — that algorithmic gap is the
konclude_ht port's job, not budget tuning. See [[project-km-panel-2026-07-05]].
