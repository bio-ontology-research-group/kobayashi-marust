---
name: project_km_sweep5941
description: "Sweep 5941 FINAL (cardfix fd94c7e binaries): 545 ok / 45 timeout / 1 memout; vs gold 544 agree / 0 INCOMPLETE / 1 unsound (11745 parallel artifact) / 0 both; 3524 = 4th giant runaway (305MB, OOM-killed driver, no gold); atmost rerun + nominal A/B in flight"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**Sweep 5941 (2026-06-12, cardfix binaries ofn ab563d2b + engine cd152a47):
545 ok / 45 timeout / 1 memout (591 records; ore_ont_3524 produced none).
Correctness vs gold: 544 agree / 0 incomplete / 1 unsound / 0 both-disagree.**

- **INCOMPLETE = 0 for the first time** — [[project_km_cardinality_recognition]]
  16461 fix confirmed corpus-wide. The ORE completeness table is now clean
  except the one unsound artifact.
- The 545-ok level (vs 564 in sweep 5690) is the cost of the
  complete-by-default configuration (d3a0e1e disjunction ordering + cardfix;
  15672 ok→timeout etc.). km medians: 0.512 s wall / 42.8 MB peak — lowest
  median memory of the five reasoners, 2nd fastest median.
- **11745 unsound (extra 5) = GENUINE unsat under-detection** (NOT a
  parallel artifact — corrected 2026-06-12). On ws the pipeline is
  DETERMINISTIC (3 runs identical sha, capped=False, no truncation) and
  reproduces 5 extra subs all of the form `GO_0008046 ⊑ {receptor-activity
  chain}`. GO_0008046 is UNSATISFIABLE in gold (in the #UNSAT block) and
  HermiT CONFIRMS it (ont + ClassAssertion(GO_0008046,p) inconsistent), so
  gold is right. KM misses the unsat and emits the class's ordinary supers.
  SAME CLASS as the 8941 ALC-forall unsat gap. ST cluster run TIMES OUT
  (orthogonal perf, not the cause).
  **ROOT-CAUSED (commit efa39c9, diagnosis only, NO fix landed).** ddmin via a
  423-axiom STAR module (ModExtract.java on unimatrix ~/minimize, bench JDK8
  javac) → 18-axiom witness oracle/ontologies/11745_unsat_core.ofn. Mechanism:
  GO_0008046 ⊑ GO_0004888⊑..⊑GO_0003674 (MF); ⊑ ∃part_of.GO_0007411, a 4-deep
  part_of chain bottoming at GO_0048856 ⊑ ∃ricdo.UBERON_0000061; part_of
  transitive; chain part_of∘ricdo⊑ridpo with domain(ridpo)=GO_0008150 (BP);
  Disjoint(MF,BP) ⇒ unsat. KM derives the MF chain + __trans__part_of__GO_0048856
  (reaches the filler) but never BP-ness ⇒ misses the clash.
  TWO isolated gaps: (1) frontend chain_clauses SKIPS pure-domain consumers of
  the chain target (empty c_on_y) — synthetic witness
  oracle/ontologies/chain_domain_propagation.ofn; fix BLOCKED by clausification
  ordering (domain_range added mod.rs pass 2, chain_clauses in augment pass 1)
  + reg.short name byte-identity invariant; needs plumbing+corpus revalidation.
  (2) composing chain recognition with TRANSITIVE part_of across hops — the
  role-chain residual, same family as [[project_km_completeness_gaps]] 9944.
  11745 needs BOTH; KM derives nothing FALSE (incomplete unsat-detection
  scored as unsound).
  **FIXED 2026-06-12 (commit b57d123, flag KM_CHAIN_DOMAIN default off).**
  augment now returns ChainInfo; after domain_range_clauses,
  domain_consumer_chain_clauses (preprocess.rs) emits the missing recognitions:
  __chain__S__ (any S-edge) + R-composition, and when R transitive the full
  __trans__ up-propagation (trans_recognition helper) so it composes across
  part_of hops. Closes BOTH gaps. Full 11745 now BYTE-IDENTICAL to gold
  (438277 subs, 1592 unsat, GO_0008046 unsatisfiable), 45.7s. Off-flag
  byte-identical; additive+sound, no Lean re-cert; 57 tests. Deployed
  ofn-chaindomain (md5 9497a713) to unimatrix ~/bench/km/; sweep 5976
  (KM_CHAIN_DOMAIN=1, res_chaindom_*.jsonl, ore_out_chaindom, distinct from
  5941 baseline) validating no corpus regression/blowup before default-on.
  Reordering passes to drop the flag is BLOCKED by the reg.short name
  byte-identity invariant; the flag is the clean carrier.
- **ore_ont_3524 = a 4th giant (305 MB)**, was killed by the node OOM killer
  with the ore_runone DRIVER at 247 GB RSS — KM's stdout exploded into the
  driver's in-memory buffer. No konclude gold exists (gold-failure ont), so
  no soundness impact, but the runaway needs a fix (suspect: engine emitting
  enormous derived_clauses/subsumptions JSON, or a stderr flood; diagnosis
  ws /tmp/diag_3524.log). Driver hardening option: ore_runone could cap
  stdout buffering.
- Gold sanity: HermiT vs Konclude differ on 4: 13503, 5940, 8135, 9540.
- **ofn byte-diff 5955 (deployed ofn vs ofn-atmost 7f8ed94)**: 581/592
  IDENTICAL; 11 DIFFER: 178, 2860 (only two currently ok — the critical
  pair), 10702, 10860(memout), 1194, 12653, 14817, 15516, 2669, 9540, 9635
  (timeouts). Rerun with ofn-atmost = job 5973
  (~/bench/ore_jobs/res_atmost_rr.jsonl); if 178+2860 stay ok+gold-equal,
  promote ofn-atmost → ~/bench/km/ofn (backup first).
