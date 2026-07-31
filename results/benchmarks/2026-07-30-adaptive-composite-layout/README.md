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
