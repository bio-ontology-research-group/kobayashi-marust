---
name: feedback_konclude_not_gold
description: "SCORING RULE — an ontology KM solves CORRECTLY counts as \"solved\" even if Konclude does not solve it; Konclude is NOT the gold/oracle for ontologies it fails"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 666845f8-0818-4d3e-8e4f-a3e9496633db
---

User HARD RULE (2026-06-27): **If Konclude does NOT solve an ontology but KM solves it CORRECTLY, that ontology counts as SOLVED.** Konclude is NOT gold for ontologies it fails on.

**Why:** Konclude is only an oracle where it actually produces a correct result. Where Konclude errors, times out, can't parse (e.g. SWRL/DLSafeRule), or returns a provably-wrong taxonomy (the contested-gold cases — ore_canon Thing≡Nothing bug, SWRL parse-fail), its output is not a ground truth to be matched. Scoring KM as "fail vs gold" there is wrong: KM's correct answer is a WIN, not a miss.

**How to apply:**
- When reporting coverage / pass counts, do NOT count an ont against KM merely because KM disagrees with Konclude. First check whether Konclude actually solved it correctly.
- Oracle precedence for "correct": cross-reasoner agreement (HermiT, ELK, Sequoia) and KM's own machine-checked calculus. HermiT was RIGHT on every proven contested ont (8941/13912/15516/2669) — see [[project_km_contested_gold]].
- "Solved by KM" = KM produces a sound+complete taxonomy (validated by an oracle that IS correct, or by KM's calculus soundness), regardless of Konclude's status.
- In sweeps: tag onts where Konclude failed / is contested separately; for those, KM's result stands on its own correctness, not on matching Konclude.
- This RAISES the real solved count: the contested SWRL onts (2669, 15516) and any Konclude-timeout/error ont KM gets right are SOLVED, not fails.

Related: [[project_km_contested_gold]] (HermiT right on contested), [[project_km_benchmark_versioning]] (gold rule + dated snapshots), docs/CONTESTED-GOLD.md.
