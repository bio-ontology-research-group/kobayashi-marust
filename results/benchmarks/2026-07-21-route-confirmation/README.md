# Fresh confirmation of documented ORE routes

This directory records the 2026-07-21 revalidation of every selected solve
route in `../2026-07-18-ore-solve-routes/ontology-solve-routes.tsv`.

The authoritative acceptance artifacts are
[`reproduced-route-ledger.tsv`](reproduced-route-ledger.tsv), its externally
hash-pinned
[`reproduced-route-ledger-receipt.json`](reproduced-route-ledger-receipt.json),
and the executable
[`REPRODUCIBILITY-PROOF.md`](REPRODUCIBILITY-PROOF.md). IBEX job `49272959`
accepted all 592 rows: 587 exact full-IRI classifications, two independently
adjudicated inconsistent classifications, and three explicit nonclaims. No
documented solve claim remains unreproduced.

The earlier registry is a union over seven hash-pinned KM executables. Most of
its rows were compared through the ORE local-name signature, which is not
injective over complete OWL IRIs. Those executables are provenance, not
acceptance evidence. This confirmation therefore uses a stronger protocol:

1. verify one current executable against its twice-built capsule receipt, while
   retaining the row's old executable hash as provenance only;
2. run the row's exact semantic environment and selected route with that
   current executable under 240 seconds,
   20 GiB process-group RSS and 16 CPUs;
3. run fresh Konclude on the same ontology and allocation under the same
   limits;
4. compute collision-safe full-IRI fingerprints for both complete named-class
   taxonomies and require exact equality;
5. for 2669 and 15516, whose stored Konclude outputs are parse-failure
   artifacts, require KM to report inconsistency and independently rerun
   HermiT on the retained contradictory subset.

Opaque historical binaries are never executed by this confirmation harness.
Their hashes and locators remain provenance only. The validator requires one
portable current executable, its twice-built capsule receipt and its source
manifest, then replays every row's exact configuration with that binary.
Historical configurations that omitted `KM_ROUTE` receive `KM_ROUTE=manual`;
this prevents the current automatic decision tree from replacing the explicit
flag bundle that constituted the old route.

The first exact-source historical cohort contains nine routes at exact Git
revision `0d20dd13312c16dec4ff256852979fb4c927556a`. For these rows, the source
identity verifier proved that all 256 build-source files equal that Git tree,
two clean offline builds produced the same executable bytes, the complete test
suite passed, and IBEX captured the runtime closure before replay. The old
retained executable was still not run. Acceptance comes from the newly rebuilt
exact source and a fresh source-built Konclude comparison.

Five more historical route claims name three other recoverable Git revisions.
Their retained source archives were checked against the exact Git trees, each
revision was built twice from closed inputs, both builds were byte-identical,
the complete test suite passed, and IBEX captured the runtime closure. Fresh
replays then confirmed ontologies 541, 7409, 7914, 12653 and 16462. The final
ledger prefers a successful current-source route when one exists, so 7409 and
16462 use their faster current alternatives while retaining the exact-source
replays as independent evidence.

An old executable that still happens to exist is not acceptance evidence. The
final confirmation capsule is built twice from the final pinned source and
archived build inputs. Any subsequent engine edit invalidates that capsule for
acceptance and requires two new clean builds. The replay record then binds the
requested route, observed route trace, complete command, closed environment,
limits, ontology, executable, source manifest and build receipt by hash.
Because `km` is dynamically linked, the validator also hashes every library
resolved by the pinned `ldd` executable on the IBEX compute node. The route
certificate rejects a different KM runtime-library count or manifest.

Current replays establish a new claim about the named route in the pinned
current source. Exact-source replays establish a claim about the named route in
the verified historical Git revision. Neither claim asserts that an unarchived
old executable was reproduced byte for byte. Any row without exact source and
reproducible build inputs remains historical provenance even when a replacement
binary obtains the same answer.

The current executable is accepted only with a hash-pinned build receipt. The
receipt names the source archive and per-file manifest, `Cargo.lock`, vendored
dependency manifest, resolved `rustc` and Cargo executables, the rustup
dispatcher, and the Bullseye container manifest digest. The three executable
hashes must be present and distinct. The receipt also records two clean,
offline, four-core release builds from the same inputs. Both builds must
produce byte-identical `km` executables. A validation task verifies this
receipt, the executable hash, and the source-manifest hash before it starts KM.

`KM_TIMING=1` is added as inert instrumentation to each current replay. The
route bundle remains the exact environment recorded in the registry. The
result record stores both environments separately and requires the frontend's
`route=<name>` trace to equal the requested named route, or `manual` for a
current-source explicit flag bundle. This proves that the intended current
route was selected rather than merely documenting what we asked KM to run.

Revision `0d20dd1` predates runtime route tracing. Its validator therefore uses
the explicit `closed-manual-environment` observation policy: `KM_ROUTE=manual`,
the complete closed semantic flag map, command, source, executable and limits
are hash-bound into a canonical identity of the form
`manual@sha256:<semantic-environment>`. A zero-trace run is accepted only under
that policy. It cannot be mistaken for a current-source trace certificate.

The 240-second and 20-GiB acceptance limits always apply to KM. A fresh oracle
may be rerun with a larger explicitly recorded memory allowance when Konclude
cannot materialize its reference taxonomy within 20 GiB; extra oracle resources
do not turn a KM failure into a pass.

When both classifiers report the ontology inconsistent, the comparison accepts
the shared inconsistency verdict without requiring the same taxonomy
serialization. KM emits no taxonomy in this case, while Konclude emits every
named class as bottom-equivalent; both denote the same explosive OWL semantics.

The three rows that are not documented as solved (4669, 10860 and 1194) are
recorded as `not_a_documented_solve_claim`; their repair work is separate. ORE
10621 is now a fresh exact full-IRI success through current route `ht_bridge`.

`selected-summary.tsv` and `selected-summary.json` are generated only from the
fresh per-ontology JSON records. Campaign completeness and solve confirmation
are separate: a provenance-valid timeout is a completed negative experiment,
but it cannot contribute a solve route. The summary also hashes an ordered
manifest of every JSON record it consumed. The final ledger verifies that
manifest, the summary hash, the aggregator hash, all validator and runner
hashes, and the complete oracle runtime closures before accepting an individual
route.

## Exact-source historical replay

The exact-source capsule is
`reproducible-0d20dd1-20260721-01`. Its two executables are byte-identical at
SHA-256 `ced4544f50a988f7a07059195ce38a6fca65f0692998c31dce656f513ad66a57`.
The build receipt is
`9a6eb331df6b86710862eef62878df082f9160f04104a242580d132ef2434ed1`,
the 256-file source manifest is
`f6b393cbda6448ccd255f1b109385134eed8b441439826b70b2e1ccd0a169537`,
and the 1,390-test receipt is
`bac2429376aad6ff2409f55b9af6a52ef162e2e6dc5fb0c48c7c6df52111d006`.
The source-identity receipt, SHA-256
`fa1810baebf9d4af5e2f78d215450ec1211c160f8c85ea00def8000a41b6964e`,
binds the build source to Git tree
`a246d2cbe4c15960189049d7c747efdebe0b148b` and Git archive
`fc817c697a808563f66db4b14cacfbc803c210ba2be3b7aae134a93fef3fce37`.
The IBEX runtime-library manifest is
`8c7fd69fcc25283170d11e2b5d9cd6c6187c9bce56f0fd4ee7654e567cb94d00`.

All nine replays completed under 240 seconds and 20 GiB. Seven full-IRI
taxonomy hashes exactly equal fresh output from source-built Konclude. For
2669 and 15516, KM and a source-built HermiT oracle independently derive
inconsistency from the retained contradictory subset, so those two rows use
the separately recorded inconsistent-ontology adjudication:

| Ontology | Documented route | Canonical observed identity | Confirmation | Wall | Peak MiB |
|---|---|---|---|---:|---:|
| `2669` | `ht_rules` | `manual@sha256:f726322d1317164c31b3348a005a59e0238bd40f36a5d1680c01dbd4ee0ee803` | adjudicated inconsistent | 0.1180 s | 16.56 |
| `6934` | `htforce_race` | `manual@sha256:0a51c30f6f0ec0541753fc7114291e5e55c5849ba271214a6ac7c9c224a4a7b0` | exact full IRI | 0.3501 s | 51.88 |
| `7499` | `card_race` | `manual@sha256:9369fce737871423b915d162c433bfed72a50d9e2b64a53a960e77543bd9a3bd` | exact full IRI | 94.0382 s | 18509.33 |
| `9540` | `card_race` | `manual@sha256:9369fce737871423b915d162c433bfed72a50d9e2b64a53a960e77543bd9a3bd` | exact full IRI | 56.1628 s | 18641.40 |
| `9635` | `legacy_tab_race` | `manual@sha256:5efe549e1abfef1777c8754fddba1e0a1bc1ab4455af5ab33cb8cb606c35e792` | exact full IRI | 0.3463 s | 68.15 |
| `10702` | `nomlink_default` | `manual@sha256:4a35a65fd3e5dbec5297e4770f12617b64a55e801e5446d41726b8c10ebe83d4` | exact full IRI | 20.3030 s | 525.68 |
| `10908` | `shoq_race` | `manual@sha256:efab0d402a24f999e4b371e7c40e6b658bbf1cfaec0401d322fbe45458bf2ac0` | exact full IRI | 0.4085 s | 233.00 |
| `15516` | `ht_rules` | `manual@sha256:f726322d1317164c31b3348a005a59e0238bd40f36a5d1680c01dbd4ee0ee803` | adjudicated inconsistent | 0.1173 s | 16.56 |
| `15672` | `shoq_race` | `manual@sha256:efab0d402a24f999e4b371e7c40e6b658bbf1cfaec0401d322fbe45458bf2ac0` | exact full IRI | 4.5735 s | 956.57 |

The immutable nine-row replay root is
`/ibex/scratch/hohndor/km/routing_20260715/source-bound-rebuilt-historical-49260043`.
Its separately frozen aggregate is
`/ibex/scratch/hohndor/km/routing_20260715/source-bound-rebuilt-historical-aggregation-49260670`.
The aggregate summary SHA-256 is
`ed3e0468847ac065c5e6c074fb923db0bf26faaf7fa208c9ef1c95bc5bc12d14`,
and the SHA-256 of its complete result-file manifest is
`06be3dcb47951f49a046f8c087eb3a04bd08c116acb55fd911a733799334a42e`.
The manifest binds nine result records with ordered-content SHA-256
`641a6c71e6fa4e2fe71046afbedd16b914130e2e6d3d1ccd18e8807a7ba73321`.

## Additional exact-source candidates

The retained source archives for three additional candidates equal exact Git
trees. The source identity verifier has SHA-256
`a5907b0af2b00d7b530edf0148a3c0aaa1016fe4d96554be2582ea31ce2f3148`.
The serialized workstation build set is
`/home/leechuck/km-repro-exact-candidates-20260722-01`; its receipt SHA-256 is
`2f354ab70f6c691f731006edb2ecce6792db0c5fdf941508977d2989762e0384`.

- `a639ab5`: commit
  `a639ab59bfb20b04f0131a2b7b7cb727117a936b`, binary
  `0bcc1e74b648a316d93a7e3d7615b8357df9dbe4dfd0aa9dde25d8e8364deb9b`,
  source manifest
  `b5240a003989b6b6331a2bbfebb71350212d8a8816bc51579a5f6266194b3c10`,
  build receipt
  `b9e1a02f45a3645809044fc7f1db0576e39e5af11c23f8842cebc70255f52377`,
  1,585-test receipt
  `9021f3aa77c400e453976499d27010f2fa31b0ef051d7a5f70bab5a9eff2550c`,
  source-identity receipt
  `8b3b6f8b0b99da154ae5c776f08ae65929dede9866cd78605970b401a4d74aee`.
- `a068059`: commit
  `a0680597525b72b9d1d2c22e5d8f4b9820d8f401`, binary
  `bf5a9f595ac5ae4ad92589710e8575633e7b7a2a043b984ef388e6fdfd3e4910`,
  source manifest
  `0023fa4897aec4ee300caa9d0bea1c15d2d9b6e9bfc7e35308f59a29e811568a`,
  build receipt
  `7fc398cf2cde7cf5f6978f5c05b7c6b080719263eb229a8e1773f4f1608bfeaf`,
  1,582-test receipt
  `c687f249ec72ce7bfc8caa9ed04d461868d5149ab41c472f6d7c7930132cb25f`,
  source-identity receipt
  `64d2f7c0a5d9676ababa4b80c94e09cdc63d8c64472e5b53ee09383059e7cb4a`.
- `a0d0148816c5`: commit
  `a0d0148816c560f79b8ed12a762feef5f0401056`, binary
  `24921722e8d7fbb989256c67a34bdc38f2bda4ffeb36a890187bd9befaf7b723`,
  source manifest
  `f81b2e785d4340b5994e43c948069c8f5c3294cf180231fb09fe47d6e658d9e7`,
  build receipt
  `d3c7d77d96daf784bf55068304a4ec333fce9817b32a0a92c985ed97f7ac1d36`,
  1,589-test receipt
  `4c9a7554db18f2383157c82b2fe41fa5781f09dd7555e31a80a4f692cd8f258d`,
  source-identity receipt
  `183e2ba8e05d01a4fe5691fec8da02e3e7f88f53f0f34ab20c088a3fdd4db986`.

All three runtime closures contain six libraries and share manifest SHA-256
`ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5`.
The immutable IBEX capsule registry has SHA-256
`fd15f3476fa6a9a58c2b59c9e00a43c36752d1ec38199d4e48f107482420caf8`;
the replay registry has SHA-256
`51b94deac0be4caa800e44b8574c397811cee3da2f2226a8e7441a5497ec1bea`.

Array job `49271944` ran every claim through route `production_all` under the
standard limits and observed exactly that runtime route. All five complete
full-IRI taxonomies equal fresh source-built Konclude:

| Ontology | Exact source | Wall | Peak MiB |
|---|---|---:|---:|
| `541` | `a639ab59bfb20b04f0131a2b7b7cb727117a936b` | 0.2564 s | 54.82 |
| `7409` | `a0d0148816c560f79b8ed12a762feef5f0401056` | 79.5919 s | 5508.23 |
| `7914` | `a0680597525b72b9d1d2c22e5d8f4b9820d8f401` | 7.1105 s | 1483.30 |
| `12653` | `a0680597525b72b9d1d2c22e5d8f4b9820d8f401` | 0.1175 s | 25.38 |
| `16462` | `a0d0148816c560f79b8ed12a762feef5f0401056` | 104.1025 s | 7594.92 |

The replay root is
`/ibex/scratch/hohndor/km/routing_20260715/source-bound-exact-candidates-49271944`.
The accepted aggregate summary has SHA-256
`262e62584fa788c7689d362636d3d6f936337bcc4d53faa54e4b0da4f9833f50`.

## Final reproduced-route ledger

IBEX job `49272959` generated the authoritative ledger from immutable selected,
alternative, exact-candidate and exact-historical evidence. Its receipt passed
every row-count, identity, provenance, command, limit and oracle check.

| Accepted state | Rows |
|---|---:|
| exact full-IRI, current selected or alternative source | 579 |
| exact full-IRI, exact candidate source | 3 |
| exact full-IRI, exact historical source | 5 |
| independently adjudicated inconsistent | 2 |
| explicit nonclaim | 3 |

The 589 reproduced claims come from 578 current selected routes, three current
alternative routes, three exact-source candidate routes and five exact-source
historical routes. The three nonclaims are 1194, 4669 and 10860. The ledger
SHA-256 is
`7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354`;
the external receipt SHA-256 is
`859614e066d0d7c890adf7c9d8d3cd4220276ae9bccf9608f24b3a6ac6e49a02`.
The immutable result root is
`/ibex/scratch/hohndor/km/routing_20260715/reproduced-route-ledger-49272959`.

Each TSV row records the exact command, closed semantic environment, requested
and observed route, 240-second/20-GiB/16-CPU KM limits, executable and source
identity, build and test receipts where applicable, runtime-library closure,
complete taxonomy hashes, fresh reference command and provenance, and the
immutable evidence locator. Run the commands captured in
[`REPRODUCIBILITY-PROOF.md`](REPRODUCIBILITY-PROOF.md) to recheck the committed
ledger without running a reasoner.

## Rejected and superseded attempts

The evidence chain is fail-closed. In particular:

- alternative-manifest preparations 01 through 04 were superseded before the
  full campaign; only the source-bound manifest with SHA-256
  `e863cdd77d10bf17e68afbd53126a55741f95c135ba9aceb53c94caa37a743f2`
  is admissible;
- smoke array `49249180` used unqualified filesystem locators. Its validator
  rejected every sampled row before loading KM, so the entire smoke root is
  non-evidence;
- coordinator attempts `49250072`, `49250199` and `49250211` failed their
  launcher preflight before starting a route-validation wave;
- exact-source replay array `49252449` produced five KM taxonomies equal to
  the fresh oracle, but the then-current validator demanded a runtime trace
  that revision `0d20dd1` could not emit. Every row was rejected. The later
  validator added the explicit `closed-manual-environment` policy and array
  `49252641` reran all five from scratch; no result from `49252449` was reused.
  That accepted five-row replay is valid partial evidence but was superseded
  after a source-revision cross-check found four omitted rows. Array `49260043`
  reran all nine exact-source routes from scratch;
- aggregation job `49260194` was rejected because its staged driver still
  expected the superseded five-row validation-driver hash. It did not alter or
  validate the nine result records. Job `49260670` used the corrected pinned
  driver and produced the accepted nine-row aggregate;
- campaign root
  `source-bound-alternatives-20260721-01-capsule10` is empty and rejected.
  Only `source-bound-alternatives-20260721-02-capsule10` may feed the final
  alternative aggregate;
- alternative finalizer `49269392` exhausted its 512-MiB allocation while
  retaining all 10,755 JSON records in memory. It produced no aggregate claim.
  Streaming aggregate job `49271931` reread the immutable records and completed
  under a separately pinned driver;
- ledger job `49272832` generated all 592 rows but its receipt incorrectly
  required newer observation columns from the older selected-route protocol.
  It emitted no accepted receipt. Job `49272911` normalized those selected
  runtime traces but did not yet normalize the three alternative records, so
  its receipt also rejected the output. Job `49272959` regenerated the ledger
  from the immutable inputs after the fail-closed normalization gained a unit
  test; all receipt checks then passed.

These attempts remain documented because a semantically plausible output is
not a reproducible claim when its source, locator, route observation or driver
identity fails.

## Alternative routes

The registry also asserts 10,755 entries under
`other_verified_exact_routes`, spanning 574 ontologies and 26 named routes.
Their retained evidence used local-name canonicalization. The original binary
still exists for 10,209 claims; the `534d5e0b...` binary used for 546
`cb_absorb_portfolio16` claims is no longer retained and its exact source
revision was not recorded.

`alternative-route-manifest.tsv` preserves that historical provenance but
replays every claim with one current hash-pinned candidate. Each replay must
finish under the same KM limits and equal the fresh per-ontology Konclude
reference by full IRI. This produces new current evidence without representing
a replacement binary as an exact replay of the missing historical artifact.

The completed source-bound manifest contains 10,755 tasks and has SHA-256
`e863cdd77d10bf17e68afbd53126a55741f95c135ba9aceb53c94caa37a743f2`.
Seven arrays produced 10,755 terminal records: 10,446 exact current-source
successes and 309 validation errors, with no missing task, mixed capsule,
route-observation or aggregate-provenance failure. Streaming aggregate job
`49271931` emitted summary SHA-256
`ef008c82b9fca9b2e6349556ac92bb391c4ab8ad5af619c700a6b4b754c40017`.

The final ledger needs an alternative only where the selected current route
does not confirm first:

| Ontology | Current route | Wall | Peak MiB |
|---|---|---:|---:|
| `7409` | `cb_plain16` | 64.1008 s | 4854.00 |
| `10908` | `production_all` | 3.2779 s | 578.86 |
| `16462` | `cb_absorb16` | 88.1870 s | 6737.13 |

Ontology 16462 has eleven exact current alternatives; `cb_absorb16` is the
fastest. The complete successful and failed alternative lists, including
commands, environments, measurements and evidence paths, are embedded in its
ledger row rather than reduced to the single selected route.

Every current result directory is keyed by the complete candidate binary hash.
The validators reject worker-binary overrides such as `KM_ENGINE_BIN` and
`KM_ELC_BIN`: the `km` multi-call executable must re-exec itself for every
worker. The strict aggregators also require one expected binary, source
manifest, build receipt, registry/manifest and validation-tool hash throughout.
Consequently an interrupted array cannot inherit a successful JSON record from
an older capsule, and records from two candidates cannot be mixed into one
claim.

For exact-gold rows the task runs and fingerprints the fresh Konclude reference
before starting KM. This makes the reference reusable even when the selected KM
route times out or fails closed, so a different named route can still be tested
without trusting the historical selected route. The compact per-class node
fingerprints and unsatisfiable-class lists from the selected KM and Konclude
runs are retained outside node-local scratch and hash-linked from the JSON
record.

`generate_reproduced_route_ledger.py` is the only producer of the final
per-ontology TSV. It ignores historical success fields. A row receives a solve
route only when a current-source JSON record has one capsule provenance, an
intact route-specification hash, an observed matching route trace, all resource
and fingerprint checks true, and exact full-IRI agreement. If the formerly
selected route fails but a freshly validated alternative succeeds, the ledger
chooses the fastest such current route and records every other current success
in the alternative-route columns. If neither succeeds, the ledger may use an
exact-source historical replay only after all rebuild, source-identity, test,
runtime and fresh-oracle checks pass. Otherwise the ontology is written as
`not_reproduced` with the fresh failure status.

The ledger keeps the historical route label, route kind, exact environment,
invocation, binary locator and hash, source revision, and evidence locator in
separate columns. These fields specify what the retained result says was run;
they cannot make that old run reproducible. The accepted columns independently
record the rebuilt command, semantic environment, route-observation policy,
capsule hashes, source identity when applicable, runtime closure, and fresh
result. A row therefore cannot blur a historical witness into a reproducible
current-source or exact-source replay.

Alternative records are also joined back to their exact manifest task and to
the hash of the selected run that produced their fresh Konclude reference. The
ledger lists every missing or failed documented alternative separately. This
prevents a successful route from being used as evidence for a different route
on the same ontology.
