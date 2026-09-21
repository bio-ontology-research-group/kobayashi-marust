# Nominal dependency of saturation cache entries

ORE 7828 misses six participle subsumptions on the native bridge. The minimized
source entails A <= B from A <= Part and exists r.{a}, Past(a), and
B equivalent to Part and exists r.Past. Adding an unrelated cardinality turns
on the completion/saturation coupling and loses that consequence.

The trace shows the nominal filler saturated with only TOP and its nominal,
flags 0x3000. The native route already declines nominal-connected cache reuse,
but the nominal saturation-rule stub never marked the dependency. Consequently
it installed this incomplete filler label as a nominal-free cache certificate.
Disabling successor expansion or cache reading restores the missing entailment.

The candidate records INDSATFLAGNOMINALCONNECTION with the existing status
propagation. It does not claim to implement complete nominal saturation. The
existing completion guard then declines that cached expansion/blocking and
ordinary completion installs the named object and assertions. Nominal-free
cache reuse remains available. This changes cache validity/scheduling, not
logical derivation rules; completion must still reach its full fixpoint.

The Lean lemmas prove the source entailment and refute a countermodel that
omits it. They do not prove the Rust flag propagation, cache guards or runtime
completion. The gate checks the actual flag, eight native classification
variants (positive/negative ABox control, cardinality scheduling, cached/uncached),
the minimized source and complete 7828 reference signature. Full regression
and release gates remain mandatory before promotion.

## Root replay follow-up

Marking the nominal saturation rule alone produced the expected 0x3008 filler
flag but did not restore the six entailments. Root initialization also replays
cached structural concepts and lacked the native nominal-connected guard. The
next candidate applies that guard before any root label/clash replay and checks
nominal occurrences reachable in the cached label's immutable concept DAG.
The same structural dependency check covers successor replay. A visited set
handles cycles. It conservatively declines this optimization; all ordinary
completion obligations remain scheduled. Runtime and performance validation
are pending. The first candidate also had a missing unit-test constant import,
which this follow-up corrects. No earlier failed candidate is promoted.
