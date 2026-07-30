# Adaptive composite-term layout candidate

The nominal CB calculus stores each grounded successor `f(o)` in one `u32`.
Its established 17-bit-individual/15-bit-function split covers ORE 15846
(129,647 individuals and 20,932 functions), but ORE 1194 has the opposite
shape: 18,055 individuals and 130,303 normalized function symbols. The fixed
layout therefore panicked before reaching a fixpoint.

This candidate profiles exact normalized function-symbol counts and source
individual counts, then selects a positional split that represents both
domains. It prefers the established 17-bit layout whenever it fits and selects
15 individual bits for 1194. The encoded order remains lexicographic by
function and then individual, every composite remains above every plain
`f(x)`, and decomposition uses the same per-worker split.

This changes representation only. It does not change rule premises,
conclusions, ordering relations, redundancy, or the derived fixpoint, so it
does not require Lean re-certification.

Source commit: `24c9612c810a070cbfcc2fac71d2c63c899d0a80`.

Source archive SHA-256:
`004de5dc1252cc80e87bd8c56315b3d18a7213ab6e2a8efb360e7f3d2d5a7eca`.

Local validation:

- the complete serial release suite passes: 1,799 library tests, eight
  ignored, all integration tests, and zero failures;
- focused tests prove layout 17 for the 15846 shape, layout 15 for the 1194
  shape, and fail closed when no `u32` split exists;
- an orchestration regression test proves source individuals are counted
  before nominal clause augmentation.

The IBEX gate must determine whether removing the representation overflow is
sufficient for 1194 to produce a complete parseable classification within 240
seconds and 20 GB. Ontology 1194 is one of the five corpus cases without an
authoritative Konclude gold, so it is not an exactness or 587-coverage claim.
The gate requires frozen-signature equality for 15846 and the other accepted
routing controls.

IBEX build job `49643820` is running. The initially submitted array `49643821`
was cancelled before execution because its harness incorrectly required a
Konclude-gold verdict for 1194. The corrected dependent array is recorded
as job `49643915`. That array was cancelled while pending because whole-node
Gold 6248 allocations could not backfill. The gate does not accept comparative
performance, so its replacement retains 16 allocated CPUs, 24 GB allocation,
the 20 GB process-tree watchdog, the CPU-model assertion, and frozen-signature
checks without requiring the entire node.

Replacement arrays `49644178` (`debug`) and `49644193` (`batch`) were
submitted without whole-node exclusivity. They share the same result paths;
the array that starts first must run alone and the other must be cancelled
before execution.

Both speculative arrays allocated index zero simultaneously, so both were
cancelled and their shared partial result directory was deleted. No output
from that collision is admissible evidence. Subsequent single-array attempts
`49644276` and `49644282` remained unable to backfill because the only Gold
6248 debug node was memory-fragmented and reserved. The correctness gate is
therefore CPU-model-neutral; its wall-time observations are diagnostic only.
The complete production sweep remains fixed to Gold 6248 CPUs.

The clean CPU-model-neutral replacement is array `49644382`, explicitly
targeted at idle debug node `cn506-11-l`. It remains queued for fair-share
priority. The older production array was briefly held after its running task
finished, then released at 363 durable ontology results; it resumes
independently and no completed checkpoint was removed.
