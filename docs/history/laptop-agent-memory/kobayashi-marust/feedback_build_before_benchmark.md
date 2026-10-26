---
name: feedback_build_before_benchmark
description: User HARD RULE — build the whole engine first with small synthetic unit tests per function; do NOT run the hard ORE onts until the engine is complete (they time out and teach nothing)
metadata: 
  node_type: memory
  type: feedback
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

For the SHIQ/SROIQ-completion engine build ([[project_km_shiq_build]]), the user
directs: **build the ENTIRE engine to completion first, validating each function
as you implement it with SMALL SYNTHETIC tests (cargo unit tests, hand-built
TInputs / tiny ontologies). Do NOT keep running the real ORE ontologies
(7914/9724/10908/15672/3215/...) during the build — they are hard and WILL time
out until everything is built, so benchmarking mid-build wastes cluster time and
yields no signal.** Run the full ORE benchmark only ONCE the engine is complete.

**Why:** the targets are inverse-bound + disjunction-heavy; no partial engine
classifies them, so a mid-build benchmark always reads as "timeout" regardless of
whether the increment is correct. Per-function synthetic tests isolate
correctness; the ORE corpus is the final acceptance gate, not a progress probe.

**How to apply:** for each engine piece (double-blocking for inverse, saturation
cache, convergent disjunction, ...), write focused cargo `#[test]` cases over
small synthetic clause sets that exercise exactly that rule (e.g. a 3-node inverse
cycle for double-blocking; A⊑∀R.C, A'⊑∃R.⊤ for ∀ soundness). Only after the full
engine is assembled do a single ORE sweep vs gold. Cancelled benchmark job
47780623 (sc3v) under this directive.

**Build host (user correction 2026-06-25):** run the per-function unit tests
ENTIRELY on **ws** — `rsync -a engine/src/ ws:km-frontend/kobayashi-marust/engine/src/`
then `ssh ws 'cd ~/km-frontend/kobayashi-marust/engine && nice cargo test --release'`.
Unit tests run where they are built, so the ws/IBEX glibc mismatch is irrelevant
here. Do NOT `cargo build`/`cargo test` on the IBEX login node (`ssh dragon 'cargo …'`)
— that is heavy compute on a shared login node and is disallowed. IBEX is only for
the FINAL ORE sweep, and that binary must be built on an IBEX COMPUTE node via
`sbatch` (ws binaries are GLIBC-incompatible with IBEX), never on the login node.
