---
name: feedback_lean_at_end
description: User rule — defer Lean re-cert to the very end; empirically solve first
metadata: 
  node_type: memory
  type: feedback
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

For the throughput/SROIQ work (and similar), do NOT treat Lean re-certification as
a blocker for implementing calculus changes. The user's explicit rule (2026-06-24):
"do NOT CARE about Lean certification now; we do Lean AT THE END, after we
EMPIRICALLY solve all the ontologies." So: implement the saturation re-architecture
(backward-∀ inverse, in-pass cardinality, etc.) behind flags, validate against the
Konclude gold sig, iterate until the onts classify sound+complete+fast, THEN do the
Lean re-cert pass over whatever the final derivation rules are.

**Why:** the CLAUDE.md "re-cert calculus changes" mandate was making me stop short of
the real fix and report instead of build. The user wants empirical solves first.
**How to apply:** when a fix changes what the calculus derives, just build + validate
vs gold; defer Lean. This matches the 7581 QoSat pattern (implement+validate, Lean
follows). Related: [[project_km_flag_sweep]], the throughput family in
docs/THROUGHPUT-SATURATION.md.