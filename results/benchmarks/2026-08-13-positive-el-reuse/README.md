# Reuse positive-EL certificate completion

The automatic pipeline previously completed positive-EL ABox materialisation
to certify consistency, discarded the resulting exact taxonomy, and then ran
the exact `elc` leaf over the same terminology again. The candidate retains
the first `ElResult` and lets only an atomic exact-EL leaf consume it. Every
injected ABox rule is rooted at a fresh internal concept, so the completion
cannot add a subsumption whose subject is an original named class. Other
mechanisms, declines, and fallbacks remain unchanged.

The release test suite passed 1,971 unit tests and all integration tests,
including the issue #3 pigeonhole regression. A new unit test compares the
named taxonomy from ordinary EL completion with the retained ABox-augmented
completion.

Paired IBEX panel `50448999` ran v0.2.15 and candidate binary `16a0d2ce…`
sequentially on the same Intel Xeon Gold 6248 node for eight of the largest
affected inputs. Every arm matched gold and its paired signature. Summed KM
wall fell from 318.52 to 242.26 seconds (24.0%); every candidate arm also used
less peak RSS.

Strict automatic sweep `50449122` produced exactly 592 terminal rows with
binary identity, profile, route trace, checkpoint, and collision-sensitive
full-IRI checks. It reports 591 successful classifications, ORE1194 as the sole
fail-closed error, 588 direct gold matches, two adjudicated consistency
mismatches, one adjudicated no-gold result, and zero behavioral differences
from v0.2.15.

The directly comparable sweep rows change as follows:

| Metric | v0.2.15 sweep | Candidate | Change |
|---|---:|---:|---:|
| Mean wall | 4.5116 s | 4.3177 s | -4.30% |
| Median wall | 0.2355 s | 0.2320 s | -1.47% |
| Mean peak RSS | 481.72 MiB | 481.30 MiB | -0.09% |
| Median peak RSS | 39.06 MiB | 39.64 MiB | +1.50% |

The median-RSS movement occurs among small unaffected inputs around the
39 MiB boundary and is run-to-run node noise, not retained completion state.
The affected eight-input paired panel reduced peak RSS in every case. This
directory contains the complete 592-row table, all paired panel rows, and the
IBEX panel and sweep scripts.
