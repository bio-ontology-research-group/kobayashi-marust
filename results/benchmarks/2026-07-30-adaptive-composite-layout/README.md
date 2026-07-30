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
sufficient for 1194 to complete within 240 seconds and 20 GB. It also checks
15846 plus accepted routing controls.

IBEX build job `49643820` and dependent focused exactness array `49643821`
are running.
