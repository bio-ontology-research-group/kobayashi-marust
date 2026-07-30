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

Array `49644382` exposed a production-only defect in the first candidate.
Ordinary `km classify` intentionally omits detailed normalized-clause
statistics, so the conductor observed zero function symbols, retained the
17-bit default, and 1194 reproduced the same overflow after 13.384 seconds at
2,800.96 MiB. This is a rejected result, not a 1194 closure. The exact controls
1034, 2237, and 6999 matched their frozen signatures. Task 15846 stopped at the
harness's expected-route assertion before classification, so it supplies no
candidate evidence.

The follow-up chooses the smallest lossless individual field whenever the
ordinary-classification meta lacks an exact function count. This maximizes the
remaining function field and cannot reduce the set of representable composite
terms. It selects 15 bits from 1194's exact 18,055 source individuals and
retains 17 bits for 15846's 129,647 individuals without scanning the normalized
million-clause vector.

Follow-up source commit: `c6bc65d6cb0b15f87eda1be165be657ce92eeb46`.
Its complete serial release suite passes with 1,799 tests, eight ignored, and
zero failures. The source archive SHA-256 is
`1a3a850c51095da64253f23feceb4fe5f9d4805669fbdf8f4c2cc788f6e0b7f8`.
Initial batch jobs `49644759` / `49644760` were cancelled while still pending.
Debug build job `49644810` and dependent five-case gate `49644811` use the
separate `adaptive-composite-layout-v2-20260731` root; build CPU model does not
enter benchmark measurements.

The v2 gate proves the representation correction reaches production workers.
1194 no longer panics at 13 seconds: it runs for 198.72 seconds before the
summed process-tree memory watchdog kills its parallel CB workers. Its parent
peak is 3,749.06 MiB, but the runner's watchdog correctly accounts for all
descendants. This removes the packed-term defect without claiming a 1194
closure. The automatic 15846 route exposed a separate router regression:
atomic `ht_bridge` reached 18,491.56 MiB and was killed after 72.17 seconds.

Forced-route control job `49645058` ran the same v2 binary on 15846 with its
known `production_all` route. It matched the frozen signature exactly in
9.6886 seconds at 903.23 MiB. The source-only large independent-ABox certificate
proves one class assertion per independent individual and excludes role,
equality, rule, data, and nominal constraints. The conductor also checks every
asserted class against the final unsatisfiable set. This supports selecting the
complete production portfolio for the certified non-EL family instead of the
atomic bridge.

Combined router source commit: `77bf385874b4fd2682aa74d3e6f230b6f7246948`.
The complete serial release suite again passes with 1,799 tests, eight ignored,
and zero failures. Archive SHA-256:
`5820e9db19c8aa50e6703f8a0390813e6d0312eff5d3bbc4d9d3ea2f81722906`.
Source-bound IBEX build `49645472` feeds exact automatic-route gate `49645473`
for 15846, 6999, 1034, 2237, 1579, and 3377.

Gate `49645473` matched 6999, 1034, 2237, 1579, and 3377 exactly. Its 15846
profile selected `nominals`, not the independent-ABox predicate: the ontology
has 129,647 individuals, 256,427 ABox axioms, role assertions, equality,
nominals, chains, and the universal role. Sixteen nominal CB workers reached
the 18 GiB summed watchdog after 80.88 seconds.

Certified-nominal control `49645724` matched 15846 exactly in 210.3321 seconds
at 18,964.77 MiB. Its complete-or-defer bridge retains the exact nominal CB
fallback but bounds the giant synchronous competitor. The follow-up automatic
gate therefore targets large nominal ABoxes by source size and excludes rules,
imports, data properties, and datatype constructors. This is a scheduling
gate, not an approximation: bridge false positives defer to exact nominal CB.

Large-nominal router source commit:
`fbb9a85ac6c4738e4cf98db59075a788c7df8d07`. Its complete serial release
suite passes with 1,800 tests, eight ignored, and zero failures. Archive
SHA-256:
`c733f1ee4a88a16b605ff8d5044f57a7531cb29a997e2aabe02dcb347ad5c145`.
Source-bound build `49646505` feeds exact automatic-route gate `49646506`.
