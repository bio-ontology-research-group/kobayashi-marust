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

Gate `49646506` passed all six frozen-signature controls. Automatic routing
selected `certified_nominals` for 15846 and matched Konclude exactly in
213.8929 seconds at 19,180.67 MiB, with 10,640 subsumptions and no missing or
extra entailments. Ontologies 6999, 1034, 2237, 1579, and 3377 also matched
exactly. The deployed binary SHA-256 is
`d5d675b850092a5dac01800978ed0f165dd403d375042bb2875b548464a9109b`.

The complete source-bound 592-ontology production sweep uses that exact
binary under array job `49646977`; dependent audit job `49646978` rejects
missing, duplicate, malformed, wrong-index, wrong-binary, and non-terminal
rows. Every classification has a 240-second timeout and a 20-GB summed
process-tree watchdog. The array explicitly requests one node from a
Gold-6248 allow-list and verifies the CPU model at runtime.

Superseded submission `49646960` and audit `49646961` were cancelled before
execution. Slurm interpreted the ten-entry allow-list as a ten-node request
until the script added `--nodes=1`; queue inspection caught this before any
benchmark row was produced.

The running sweep exposed an automatic-route regression on 1481. Its source
profile is a 1,302-axiom typed object-ABox in SOI with no number restriction
or datatype. `certified_nominals` reached the 20-GB process-tree cap after
64.2317 seconds, although the frozen complete route matrix records many exact
closures and `production_all` at 0.4 seconds. This is a route-selection
failure, not a missing reasoning procedure.

The follow-up feature rule sends typed object-ABoxes with neither ordinary nor
qualified cardinality and no datatype to `production_all`. Cardinality-bearing
SHOIN inputs and atomic datatype TBoxes retain `certified_nominals`; the giant
15846 profile retains its separate large-nominal gate. Both portfolios keep an
exact nominal-aware fallback, so this changes scheduling only. The complete
serial release suite passes with 1,801 tests, eight ignored, and zero failures.
Current-binary forced-route control job `49647712` is pending on IBEX.

Follow-up source commit: `80eb1d4`. Its source archive SHA-256 is
`c6690d08a3ccb9163638a3d0fbd9fa64c5d4bfe0a24ab62f85f4743274b10ea4`.
Source-bound build job `49648746` feeds five-case automatic-route gate
`49648747`, covering 1481, the retained cardinality-bearing 15672 and giant
15846 routes, and production controls 6999 and 1034.

Build `49648746` produced binary SHA-256
`2744c876b2e9d31d6b8924c5b0fe4c683e16c5421537ae9d854a36fe5e5a8127`.
The gate confirms automatic 1481 is restored: `production_all` matches exactly
in 0.9659 seconds at 225.69 MiB. Retained controls 15672, 6999, and 1034 also
match exactly. Giant control 15846 retains `certified_nominals` and matches
exactly in 177.4123 seconds at 19,100.21 MiB. Gate `49648747` therefore passes
all five cases.

Complete v5 array `49649240` is source-bound to that accepted binary and waits
on `afterok:49646978`, the strict v4 audit. This preserves an uncontended v4
baseline before the next 592-ontology iteration begins. Dependent v5 audit
`49649241` runs after every v5 array task reaches a terminal state.

The v4 baseline next exposed 3524 as a 20-GB memout. Historical current-route
evidence solves this 1.97-million-axiom flat taxonomy exactly with both
`production_all` and `elc`, with `elc` fastest at about 19 seconds and 2.6 GB.
Current-v5 route comparison array `49649529` reruns both candidates against
the frozen Konclude signature on Gold 6248 CPUs.

The source profile for 3524 contains 1,974,320 `SubClassOf` axioms and
123,311 named-class declarations. It has no ABox, RBox, Boolean class
constructor, role restriction, cardinality, nominal, or datatype structure,
and its maximum concept depth is one. External expressivity flags report
inverse roles and transitivity despite the absence of role axioms, so the
router now recognizes the source structure directly. The performance
threshold applies only to million-edge flat taxonomies; ELC still validates
the normalized fragment before reasoning.

The source predicate matches only 3524 in the 592-ontology profile table.
Routing commit `2faf2ce` selects ELC for that predicate. Its complete serial
release suite passes with 1,802 tests, eight ignored, and zero failures.
Source archive SHA-256:
`1876fc4f4eef6d5999c590faccd7445c83acb635bf79e6679385b5a7e9814d27`.
Source-bound build `49650190` feeds six-case exact automatic-route gate
`49650191`: 3524 must select ELC, 1481 must retain `production_all`, and
15672, 15846, 6999, and 1034 must retain exact classifications.

Gate `49650191` rejected 3524 before classification because its authoritative
current profile selected `production_all`. Profile capture job `49650378`
identified the mismatch: the frontend reports 123,313 bottom occurrences even
though the complete source axiom-type inventory contains only `Declaration`
and `SubClassOf`. Bottom concepts are part of EL and ELC validates the
normalized fragment independently. The corrected predicate therefore permits
bottom concepts while continuing to reject bottom roles, ABox, RBox, Boolean
constructors other than bottom, restrictions, cardinalities, nominals, and
datatypes. The other five gate cases passed, including exact 15846 in 174.9937
seconds at 18,946.9 MiB.

The v7 automatic gate selected ELC for 3524, but the ordinary benchmark runner
was then cgroup-OOM-killed during local-name canonicalization. Diagnostics with
24, 32, 64, and 128 GiB separated the stages:

- The current frontend emits a 353,051,472-byte clause file at a 1.98-GiB
  peak. Its SHA-256 is byte-identical to the historically exact frontend.
- Current and historical ELC workers both complete that exact input in about
  5.3 seconds at about 2.48 GiB and emit byte-identical output.
- Direct `km classify` completes at about 2.48 GiB.
- The collision-unsafe ORE local-name projection is the failing component.
  Ontologies 3524 and 15703 already have a documented full-IRI-only benchmark
  path because that projection collapses distinct nested IRIs and previously
  required more than 235 GiB.

Collision-safe full-IRI gate `49651828` classifies 3524 through ELC in 18.4848
seconds at 2,589.8 MiB. Its 1,604,386-subsumption fingerprint is
`090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a`,
exactly matching the established Konclude full-IRI fingerprint. The
fingerprinting step is postprocessing and is reported separately: 15.9954
seconds at 902.61 MiB.

ELC computes bottom propagation in its own complete fixpoint. The frontend
therefore skips the general SROIQ bottom prepass on the two ELC-only routes.
All other routes retain it unchanged. This avoids redundant giant-taxonomy
work without changing the normalized ELC answer or the calculus.

The bottom-aware source is commit `bf38a8d`; its archive SHA-256 is
`521f57a95660b5a8f3b320441cacf2e59be55a18570ea89e034c1eaef2b216af`.
Source-bound build `49651896` produced binary SHA-256
`727f91c62cf28cda1a91d0ebc0d07b40cefe594914b11c4ed9eacd30a1e7cdff`.
The ordinary five-case v8 gate passed, including exact 15846 in 189.5256
seconds at 18,844.32 MiB. Automatic full-IRI gate `49651898` selected ELC for
3524 and matched exactly in 20.0688 seconds at 2,564.38 MiB.

The production sweep selects a full-IRI-safe runner for 3524, 13503, and
15703. The first and third have non-injective local-name projections; 13503
has a legal named source class ending in `#Nothing`, which the local-name
signature mistakes for OWL bottom. The runner leaves reasoner timing and
process-tree RSS measurement unchanged,
skips the non-injective local-name closure, fingerprints the retained full-IRI
answer, compares it with the established Konclude fingerprint, records the
result in the terminal row, and deletes the large taxonomy. Wrapper gate
`49652266` passed end to end for 3524 in 18.3166 seconds at 2,581.45 MiB.

Complete v8 array `49652271` and strict audit `49652272` replace the cancelled,
never-started v5 array and audit. The v8 array remains held on
`afterok:49646978` so the v4 baseline finishes without resource competition.

Current-v8 residual route array `49652352` tested feature-compatible exact
portfolios for the first failures exposed by the partial v4 baseline. It
restored three cases:

- 9654: `production_all`, exact in 10.7848 seconds at 1,198.05 MiB.
- 9724: `production_all1`, exact in 33.0192 seconds at 10,234.14 MiB
  (`production_all8` is also exact but slower and larger).
- 7499: `certified_card_proxy_abox`, exact in 96.5817 seconds at 1,088.96
  MiB. This remains an explicit measurement route because it drops the ABox
  and does not yet carry the consistency and ABox-irrelevance certificates
  required for safe automatic selection.

The next scheduling patch sends large nominal ABoxes without cardinality or
datatype constructors to the complete production portfolio after the earlier
large-nominal bridge gate. This catches 9654’s data-property ABox while
retaining 15846 on `certified_nominals`. It also sends large Horn functional
terminologies with at least 100,000 clauses and 10,000 function symbols to the
one-thread production portfolio, recovering 9724 below the memory cap. Both
changes select existing exact portfolios and do not change derivations.

The scheduling source is commit `784a36e`. Its complete serial release suite
passes, including dedicated positive and negative routing tests and the
retained large-nominal controls. The source archive SHA-256 is
`0a7162a46b8de15588169b93baa67cf3b528f867f943b83ae17175db12730d33`;
source-bound build `49653229` produced binary SHA-256
`888e2e1fa9314a87069a0b022facf4856100c7e2d210ff938567252a5634007f`.

Automatic-route gate `49653230` matched the frozen Konclude signature on all
five ordinary controls:

| Ontology | Selected route | Wall seconds | Peak MiB | Result |
|---|---:|---:|---:|---:|
| 1481 | `production_all` | 0.9985 | 224.79 | exact |
| 15672 | `certified_nominals` | 0.2127 | 39.81 | exact |
| 15846 | `certified_nominals` | 178.3469 | 18,786.23 | exact |
| 9654 | `production_all` | 12.0373 | 1,198.39 | exact |
| 9724 | `production_all1` | 37.5402 | 16,294.18 | exact |

Collision-safe automatic gate `49653231` also matched 3524's established
full-IRI Konclude fingerprint in 19.8445 seconds at 2,582.70 MiB.

Complete v9 array `49654040` and strict audit `49654041` were held before
execution and then canceled when the exact v10 gate passed. They produced no
benchmark rows.

Full-IRI-safe gate `49654146` validates the third special case end to end.
Automatic 13503 finishes in 0.0407 seconds at 8.37 MiB, with 113
subsumptions, one unsatisfiable named class, and exact fingerprint
`1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b`.
The ordinary local-name scorer's extra-bottom report is therefore a projection
artifact.

Late v4 residual probes against the accepted v9 binary recover three more
known mechanisms:

- 6934: documented `htforce_race`, exact in 0.1896 seconds at 55.46 MiB.
- 10702: documented `htforce_race`, exact in 0.5018 seconds at 154.22 MiB.
- 10908: `production_all`, exact in 204.5211 seconds at 1,094.00 MiB.

Forced HT remains measurement evidence, not an automatic route: its bypassed
datatype/nominal guard needs a semantic certificate before policy admission.
Current `production_all` still times out on 12653 at 240 seconds. The ordinary
13503 row repeats the known local-name artifact; the full-IRI-safe gate above
is authoritative.

The next scheduling candidate recognizes small ABoxes containing only class
assertions and explicit identity constraints in a qualified-cardinality
terminology. It selects the complete production portfolio, which retains the
same exact nominal-aware CB fallback, and targets 10908 without an
ontology-name test. The predicate matches only 10908 in the frozen 592-profile
table. Its complete serial release suite passes with 1,814 library tests, eight
ignored, and all integration tests passing.

The accepted scheduling source is commit `9ef5106`. Source-bound build
`49654854` produced binary SHA-256
`3b5cde49b6ed3f759be585ed08ecbdec51e4327c4f31ba23427678529a129208`;
the source archive SHA-256 is
`96b6adc4c1d2391f92da45bfd1d5e53ad69985e438333da6b6687e13ef7eb566`.
Gate `49655059` passed all five automatic-route cases exactly:

| Ontology | Selected route | Wall seconds | Peak MiB | Result |
|---|---:|---:|---:|---:|
| 10908 | `production_all` | 204.6423 | 1,016.07 | exact |
| 9654 | `production_all` | 11.4120 | 1,199.31 | exact |
| 9724 | `production_all1` | 35.7287 | 16,425.73 | exact |
| 1481 | `production_all` | 0.9851 | 225.86 | exact |
| 15846 | `certified_nominals` | 188.3523 | 18,927.86 | exact |

The complete v10 production sweep is array job `49655276`, with strict
dependent audit `49655277`. The deployed package contains the accepted binary
and source archive, all runner dependencies, a SHA-256 manifest, import
preflights, resumable terminal checkpoints, and the full-IRI-safe path for
3524, 13503, and 15703. This sweep is the authoritative test of the automatic
feature-driven portfolio; the focused gate alone is not a corpus-wide coverage
claim.

The array produced all 592 terminal rows, and dependent audit `49655277`
passed. An independent strict audit verified the package manifest, 592 unique
ontology names, 592 byte-equivalent terminal/checkpoint pairs, 592 successful
route profiles, the array-job provenance, and the deployed binary SHA-256 on
every row. The result is 583 `ok`, five `error`, two `timeout`, one `memout`,
and one `unsupported`; verdicts are 581 exact `match`, two independently
adjudicated stale-gold consistency mismatches, and nine unresolved execution
failures. The unresolved set is 1194, 4669, 6934, 7499, 9724, 10702, 10860,
12653, and 15803. Current source separately restores 9724 and 15803, subject
to the new source-bound gate and the next complete sweep.

Its terminal row for 3215 confirms that the historical restoration is now part
of the automatic portfolio. `production_all` matches the frozen signature
exactly in 169.5591 seconds at 7,490.09 MiB, with 3,923,171 subsumptions and no
unsatisfiable named classes. The result is bound to v10 binary SHA-256
`3b5cde49b6ed3f759be585ed08ecbdec51e4327c4f31ba23427678529a129208`.

Ontology 7914 is also restored automatically by the same frozen binary.
`production_all` matches exactly in 45.8956 seconds at 1,563.54 MiB, with
141,517 subsumptions and three unsatisfiable named classes.

The same sweep shows that 6934 is not yet restored automatically. The profile
selects `nominals`; its engine worker exits after 190.2287 seconds at
1,517.47 MiB without a taxonomy. Current guarded `ht_features` and `ht_full`
defer, while `certified_nominals` and `production_all` time out. The retained
`htforce_race` classification remains exact in under one second, but it
bypasses the completion guard and is measurement evidence rather than an
automatic route contract. v11 must therefore remain held while 6934 is either
given a sound feature certificate or retained as an explicit regression.

Source-bound trace job `49658482` localizes the missing certificate. Conversion
drops no clauses, but records four fences: inverse functionality,
nominal+inverse interaction, inverse+number interaction, and an incomplete
nominal ABox because 624 data-property assertions have no typed completion
representation. Bypassing only the outer gate runs the generic HT worker and
returns, but it does not discharge those four obligations. A sound restoration
therefore needs exact typed data-assertion/ABox handling together with the
combined inverse/number checks; changing the feature router alone would admit
an uncertified approximation.

The v10 sweep also confirms that 7499 is not automatically restored. It selects
`nominals` and exits after 190.3972 seconds at 2,967.96 MiB. The explicit
`certified_card_proxy_abox` mechanism remains exact, but its certificate proves
only number-role separation (`card_number_role_separable=true`); the ABox is
not materializable or proven TBox-irrelevant, and complete consistency is not
established. Automatic admission therefore requires either a complete
ABox-irrelevance plus consistency certificate or the missing qualified
cardinality inference in the exact CB path.

Specialist sweep `49654935` found no additional ordinary route for 12653.
`ht_full`, `ht_features`, and `elc_cert` reject its feature set.
`cb_plain1` ended in an engine error after 190.1029 seconds at 21.77 MiB.
The separately measured forced-HT closure remains diagnostic evidence until
its bypassed guards have a semantic certificate.

Diagnostic job `49657115` confirms why the historical bridge closure is not
currently admissible. The conversion is lossless at the clause count level
(`dropped=0`), but records nine exact source-side complex-domain fences plus
an inverse+number fence. More importantly, the ontology combines inverse
roles and qualified number restrictions with decimal, integer, and
positive-integer data-role constraints. The current completion bridge has no
typed data-domain object and therefore defers rather than interpreting those
datatype fillers as ordinary object classes. Restoring the older fast answer
requires an exact combined datatype/cardinality bridge certificate or
implementation; simply removing the newer fence would revive a known
fail-open path.

The next source-feature rule recognizes a terminology with at least 100,000
TBox axioms and a tiny ABox containing only class assertions plus explicit
identity constraints. It excludes imports, rules, role assertions, datatype
constructors, data properties, and cardinality. The complete production
portfolio retains the exact nominal-aware fallback, so this changes scheduling
without changing a derivation. In the frozen 592-profile table it changes
15803 and retains the already-production-routed 6722 control; it contains no
ontology-name or fingerprint test.

Source commit `bc3a9ab` passes the complete serial release suite: 1,807 library
tests pass, eight are intentionally ignored, and every integration test passes.
Its source archive SHA-256 is
`6a6d10def5b48a0d8361768067ae5f000a74ef0c39b1bc75e53eb5d3840ace7f`.
Source-bound build `49656233` produced binary SHA-256
`cb492d92948460671c07cb08029d188b03f0c43809efe837c70918cd4b9f08c5`.
Exact automatic gate `49656234` passed both cases:

| Ontology | Selected route | Wall seconds | Peak MiB | Result |
|---|---:|---:|---:|---:|
| 15803 | `production_all` | 32.8165 | 2,600.87 | exact |
| 6722 | `production_all` | 7.0989 | 1,096.98 | exact |

The complete v11 sweep package is staged at
`/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-full-20260731`.
It binds the binary and source archive above to the same strict runner,
collision-safe full-IRI checks, terminal checkpoints, import preflight, and
dependent corpus audit used by v10. `SHA256SUMS` verifies every executable,
source, runner, canonicalizer, and audit input. The v11 array is intentionally
not submitted until the v10 audit accepts all 592 terminal rows, so the two
production sweeps cannot contend for the fixed benchmark nodes.

Before submission, the v11 resume and audit contract was tightened further.
A resumed task skips execution only when both its terminal row and route
profile validate; an interrupted pair is rerun. The dependent audit verifies
the package manifest, all 592 terminal/checkpoint pairs, every route profile,
and every row's deployed-binary SHA-256. A Slurm OOM recovery now publishes
the same independently evidenced row to both terminal locations. Each task
writes and validates its feature profile before classification, so even a
worker-level OOM cannot publish a result without its route evidence.
The audit also requires every non-`ok`/`match` outcome to equal an explicit
`ontology:status:verdict` adjudication supplied at submission. It reports
status and verdict distributions plus the complete non-match map, and fails
both unexpected regressions and expected residuals that silently change state.

The v10 sweep's 4669 timeout is expected, not a scheduling regression. Current
KM rejects the historical bridge result because targeted satisfiability checks
disproved that taxonomy. No validated route currently closes 4669, and it
remains an explicit residual rather than being counted from a known-unsound
historical output.

The complete v10 sweep also exposes a memory-stability problem for 9724.
The focused automatic gate completed `production_all1` exactly in 35.7287
seconds at 16,425.73 MiB, but the same frozen binary and CPU model reached the
20,480 MiB watchdog limit during the corpus sweep after 32.2641 seconds.
The full-sweep row is therefore a real `memout`, not an accepted restoration.
One successful run does not provide enough headroom to make this route a safe
automatic choice under the benchmark contract.

Repeated source-bound panel `49659468` runs five independent
`production_all1` trials and five `production_all8` trials for 9724 using the
v11 binary, the same Gold 6248 node set, 240-second timeout, and 20,480 MiB
watchdog. It depends on completion of v10 array `49655276`, so it cannot
contend with that sweep. Every trial publishes a terminal checkpoint for an
exact, timeout, memout, error, or unsupported outcome. The panel will determine
whether either complete production route has reproducible memory headroom; v11
remains held until this evidence is available.

The route ledger also contains earlier exact `ht_bridge` and `ht_full`
measurements near 8.2 GiB. Those named routes use the current structural guard
and do not set `KM_HT_FORCE`, but the historical measurements alone do not
establish their behavior in the v11 binary. Companion source-bound panel
`49659697` therefore runs five trials of each guarded HT route under the same
9724 contract and the same dependency on v10. An exact, reproducible guarded
HT result would provide substantially more memory headroom than
`production_all1`; a defer or mismatch will keep it out of automatic routing.

Both repeat panels completed with 10/10 exact classifications. Five
`production_all1` trials used 10,407–10,524 MiB in 38.85–39.55 seconds.
Five `production_all8` trials used 16,706–20,048 MiB in 39.70–56.01 seconds,
which leaves little memory headroom. Five guarded `ht_bridge` trials used
8,169–8,194 MiB in 37.96–39.35 seconds, and five guarded `ht_full` trials used
8,158–8,174 MiB in 38.00–45.17 seconds. Every row has signature SHA-256
`95d679d0ee51b14583ca4dffe419b1c7e128398d207a2bdb25ab9eaa06c03b05`.
This establishes the guarded bridge as the reproducibly lowest-memory exact
route in this panel.

Local current-source diagnostics identified why v10's automatic 9724 route
still used the high-memory portfolio. Automatic selection runs immediately
after source parsing, before clause statistics exist. The old scheduling
predicate required at least 100,000 normalized clauses and 10,000 function
symbols, so it was unreachable during production classification even though
the post-normalization `km profile` command reported `production_all1`. A
timing trace confirmed the mismatch: the diagnostic profile selected
`production_all1`, while `km classify` actually launched `production_all`.

The corrected predicate uses only pre-normalization OWL features: a large
terminology with at least 30,000 logical axioms and 100,000 concept
expressions, functionality, and no ABox, import, rule, union, complement,
disjointness, cardinality, or datatype construct. The frozen 592-profile table
matches only 9724. This remains structural dispatch and contains no ontology
name, index, or fingerprint. Its selected `ht_bridge` worker independently
requires lossless converted-input coverage and is complete-answer-or-defer.

Current-source binary SHA-256
`a07dcffe7b509d7cb72794b55f763ec6e72bc1305614d8404fe38acebd4a5ce8`
then selected `ht_bridge` in the production timing trace. The same binary under
`KM_ROUTE=auto` matched the full-IRI Konclude signature exactly: 457,090
subsumptions, no unsatisfiable named classes, zero extra/missing pairs, 40.5751
seconds, and 8,184.64 MiB on `leechuck-office`. Explicit guarded controls were
also exact at 8,165.19 MiB (`ht_bridge`) and 8,150.66 MiB (`ht_full`). These
local results establish the routing mechanism and signature but do not replace
the queued source-bound IBEX repetitions or a complete corpus sweep.

The first IBEX gate attempts, jobs `49662044` and `49662671`, correctly
rejected a workstation-built binary before classification because it required
glibc 2.39 while the allocated IBEX node provided glibc 2.34. The zero-work
runner row records this as an error with a missing route trace. The replacement
gate builds commit `f6b2188` from source in a Slurm build job, publishes the
cluster-compatible binary SHA-256, and makes classification depend on that
successful build. The source-archive SHA-256 is
`b8febb611fd088867960b07fca70e75a1c59ac6922026657f02be682de274239`.
Build job `49662845` completed on IBEX and produced binary SHA-256
`bac80ee342b621730cdc28d1d0a1f6616be7ee0da3fda35db2a6f69fc14806ec`.
Gate `49663014` is pinned to the same Gold 6248 node set used by the complete
sweeps and explicitly verifies the CPU model before classification. It passed:
production selected `ht_bridge` and matched exactly in 38.5499 seconds at
8,169.19 MiB, with binary SHA-256
`bac80ee342b621730cdc28d1d0a1f6616be7ee0da3fda35db2a6f69fc14806ec`
and signature SHA-256
`95d679d0ee51b14583ca4dffe419b1c7e128398d207a2bdb25ab9eaa06c03b05`.
The measured classification must record `route=ht_bridge` and pass the
collision-safe full-IRI comparison under the 240-second/20,480-MiB contract.
The hardened runner sets `KM_TIMING`, extracts the route selected at the real
production frontend boundary, and records it as `selected_route_trace`; this
prevents a post-normalization diagnostic profile from being mistaken for the
route that actually ran.

The next complete source-bound sweep is array `49663016`, with dependent audit
`49663017`, under
`/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-full-20260731`.
It depends on successful gate `49663014`. Every measured row captures the
actual production route; resume validation and the final audit reject a row
without that trace. Ontology 10860 is the sole explicit missing-trace
exception because its unsupported DL-safe rules stop the frontend before a
route can be selected. The package manifest binds the IBEX-built binary,
`f6b2188` source archive, runners, full-IRI wrappers, canonicalizer, watchdog,
array script, and audit script.
