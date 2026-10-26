---
name: feedback_no_benchmark_hardcoding
description: "Hard rule: NEVER hardcode ontology ids / condition on the benchmark set; only general structural rules"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-16 (user, emphatic, "This must NEVER happen!"): **NEVER hardcode any
ontology identifiers in KM's code, and NEVER condition on knowledge of the
benchmark set (ORE ont ids, gold answers, per-ont whitelists).**

**Why:** conditioning on the benchmark is cheating — it produces a reasoner that
"works" only on the known corpus and is unsound/incomplete on anything else. KM
must be a general SROIQ/OWL2-DL reasoner. The target is a real Konclude
competitor, not a benchmark-overfit.

**How to apply:** routing/optimisation decisions may ONLY use general structural
properties computable from the ontology itself (e.g. "is ALC(H)", "has a
transitive role", "disjunction density", "number restrictions present",
clause/concept counts, fragment membership). A condition like
`if transitive && alc { route to KM_HT }` is fine; `if ont == "5303"` or a
whitelist of validated ont ids is FORBIDDEN. When a fix is validated on specific
onts, generalise it to the structural rule that explains WHY it works, then
condition on that rule. This is why the "validated whitelist" deploy option was
rejected in favour of fixing the 5303 completeness gap generally
[[project_km_hermit_trace]].
