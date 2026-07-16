# ORE 2015 expressivity, procedure matrix, and learned routing

This directory records the 592-ontology IBEX experiment used to select KM's
default classification procedure. It contains the submitted scripts, the exact
Konclude-compatibility witnesses, the per-ontology structural table, and the
analysis that generates a source-only decision tree. Final matrix and routing
validation results are added here after the Slurm gates finish.

## Current post-source-symbol matrix run (2026-07-16)

The current full rerun uses portable KM binary
`c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6`
and matrix runner
`3b1d2a878cae0e79f66de34fed4cd5c9dce1e457c958a5ce10d579217549c9d0`.
IBEX smoke job 48946056 first required exact Konclude signatures for ORE 8864,
12009, and 6817 through `cb_plain16`, then for 148, 178, and 11016 through the
exact `nominals` route. All six match with zero pair, unsatisfiability, or
consistency differences. The release suite reports 1,515 passed, 0 failed,
and 7 ignored.

Full array job 48946164 starts all 592 ontology panels, with 24 isolated KM
mechanisms and four external baselines per panel, in 50 shards. It writes only
to the initially empty `matrix-results-c229366f/`, `failures-c229366f/`, and
`manifests-c229366f/` directories. Every reasoner process retains the 240
second and 20 GiB limits. The Slurm wrapper has 192 GiB because canonical
closure of the 600–680 MB source ontologies 3524 and 15703 exceeded the former
64 GiB envelope after each capped reasoner had exited. Wrapper memory is not
included in a reasoner's recorded process-group peak RSS.

The preceding post-148 array 48943875 and its 192 GiB tail retries 48944499 and
48944228 were cancelled after 128 complete panels. Its corrected canonicalizer
removed four false disagreements, but exposed a real completeness family:
legal source classes beginning with `__` were confused with KM-generated
symbols and never received query contexts. Sequoia keeps these symbol kinds
separate. KM now gives registry-owned source names a collision-safe internal
escape while preserving their exact public IRIs. The quarantined
`matrix-results-bf2875c9/` rows are diagnostic only and never train the tree.

The profile corpus hash used for policy learning is
`94b370575c9d54f13da3bc584ef9f0c341b0e808afe7937653657db81a8278c0`.
It preserves 589 immutable profiles and replaces only the three DL-safe-rule
profiles with current-binary records carrying `unsupported_rule_axioms`.
Profile job 48944185 found four unsupported rule axioms in 10860 and none in
15516 or 2669. Profile analysis job 48944597 regenerated all 592 rows from that
corpus, retaining 592/592 exact Konclude expressivity codes and recording four
unsupported rule axioms in total. Tree training, Rust emission, and the final
paired automatic route sweep remain gated on complete matrix panels.

Assertion-heavy follow-up job 48946944 measured the exact nominal calculus on
10697, 15725, and 15846 under central single-thread and per-function 1, 8, and
16-thread schedules. Every one of the 12 runs reached the 190 second internal
cap or the 240 second harness cap. Official Konclude trace job 48947466 then
localized the architectural difference: Konclude finishes ABox consistency
precomputation once and spends only 2 to 80 ms in the following class
classification. These diagnostics motivate profile-schema-2's fail-closed
`positive_abox_tbox_separable` certificate. The frozen c229 matrix remains
valid mechanism data; a new profile corpus and final automatic-route validation
will use the version-2 certificate after this matrix completes.

## Immutable inputs

Five superseded arrays are retained as audit artifacts and never enter the
training data. The first exposed a missing procedure gate:

- Superseded KM binary: SHA-256
  `969147ccb3ddac190d63a3de836df78352ce722efd726753a4359e6f3ff5610b`.
- Superseded matrix submission: SHA-256
  `b61fe627e71210b9bfdee0483ec489ab479bace3c8da7325aa4593a528a068ec`.
- Superseded IBEX job: `48873174`, cancelled at 285 complete ontology panels,
  23 partial panels, and 6,223 rows.

That binary did not implement the `KM_NO_ELC` master gate even though the
matrix supplied it to the pure-CB and HT arms. Those rows therefore measured a
different procedure on EL-safe ontologies and could invoke the certified-EL
portfolio on other inputs. The analyzer does not read `matrix-results/`.

The second array implemented that gate and pinned `KM_ROUTE=manual`, but its
closure audit exposed a later orchestration regression. Exact source-RBox
provenance fenced 541's complex domain and range for the legacy tableau. The
orchestrator mistakenly applied the same fence to the source-TBox Konclude
bridge, even though the exact bridge kernel classified 541 immediately when
invoked directly. Job `48879104` was cancelled at 376 complete panels, 19
partial panels, and 8,063 rows; certificate-corrected replacement job
`48881097` was cancelled before starting. Its binary SHA-256 was
`0854c99a0b6fd62e3c230ecee1dd7b4167cf926b53527f0a4a4b5e6bc6e0685c`.
The analyzer does not read `matrix-results-gated/`.

The third attempt repaired that bridge gate and added the historical closure
controls, but the option audit caught one more procedure-definition error. Its
`tab_race` row set only `KM_TAB_RACE`; the newer outer certified-EL portfolio
prevented the older CB-stack branch from being reached, and the row omitted
`KM_TAB_FEAT`, which admits otherwise faithfully encoded inverse-only or
number-only inputs to the legacy racer. Job `48884182` was cancelled at 112 complete panels,
20 partial panels, and 3,118 rows. Its binary SHA-256 was
`943748d91fa150dc68f393d4c9459b0adc9b3b29e91c646f88d5819d8556b2ca`, and its
submission SHA-256 was
`17dca46e613435dc7dbcc429064ab20e23ce0de779df1d6c38392943ead2fabf`.
The analyzer does not read `matrix-results-final/`.

The fourth attempt made the tableau procedure real and passed its targeted
gate, but a final static procedure audit caught unsafe fallthrough inside four
policy-eligible names. `ht_qo`, `ht_shoq`, `ht_card`, and `ht_bridge` activated
their specialist, but if its structural candidate was absent they silently ran
the unrestricted general HT racer. That racer is an explicit measurement arm
because it is incomplete on part of ALC+disjunction; it cannot safely hide
under a specialist name. Array job `48890044` and dependent analysis job
`48890355` were cancelled at 25 complete panels, 5 partial panels, and 686
rows. Its binary SHA-256 was
`8cc7e138ae8ae3b942e391673c2f08bcdc91dbff29cf66e2a202b243a4f561e1`.
The analyzer does not read `matrix-results-final2/`.

The fifth attempt used the definitive binary and procedure panel, but an early
partial audit found a defect in the experiment's KM-output shortcut. Ontology
412 contains distinct full IRIs that share local names. The shortcut computed
the transitive closure over full IRIs and only then collapsed local names;
ORE's retained Konclude signatures collapse local names first and recompute
SCCs and transitive closure. This ordering difference falsely reported 28
missing pairs for all KM procedures on 412. Array job `48892360` and dependent
analysis job `48892362` were cancelled after 36 result files had appeared. The
rows and diagnostic artifacts are quarantined in
`matrix-results-final3-precanon-20260715T132248/` and
`failures-final3-precanon-20260715T132248/`; no analyzer reads them.

Both benchmark runners now import the exact gold-generating ORE canonicalizer,
which is byte-identical to `oracle/ore/ore_canon.py`. Every result row records
its SHA-256, and both analyzers reject absent, mixed, or unexpected
canonicalizers. IBEX regression gate `48894378` reran ontology 412 on one Gold
6248 node: KM returned an exact match with zero pair, unsatisfiability, or
consistency differences between paired one- and 16-worker Konclude references.

The definitive source-only bridge gate admits complex domain/range fences only
when a complete normalized source TBox is present. It keeps the reconstructed
clause path fenced. An explicit tableau race now suppresses the shadowing outer
EL portfolio, and its named bundle enables the legacy feature gate while
disabling the unrelated outer HT racer. It still respects `cb_to_ht`'s stricter
`inverse+number(SHIQ)` fence. Every policy-eligible route begins with
`KM_HT_ONLY=certified`, which admits only the Konclude completion bridge's
complete-answer-or-defer path. The four HT specialist names narrow that
discriminator to their exact procedure. A nonmatching input defers to CB;
bridge-only mode also forbids the worker's internal legacy-tableau fallback
after a bridge defer. General HT, QO, SHOQ, first-class cardinality, and the
historical tableau remain explicit measurement rows but cannot become tree
leaves because they have documented incompleteness or no complete-procedure
contract. The final matrix includes every
still-supported historical ORE closure lever missing from the 19-arm diagnostic
panel.

- Corpus list: 592 entries, SHA-256
  `7849b4b875d3b9bc5e214b67a1fa584f3d684e595954ca11a816448c87d3d2b8`.
- Definitive KM matrix binary: SHA-256
  `e1bcc9671b3af044805516efc29f92f197ff99e2c277f78040ee6b731e2d98dc`;
  maximum required GLIBC version 2.29.
- Official Konclude binary: SHA-256
  `5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3`.
- Matrix runner: `bench_one_matrix_frozen.py`, SHA-256
  `e948d47b89549664368ad9222f287d030a078e67b5387da0a00d7e6de4463daa`.
- Exact ORE canonicalizer: `ore_canon.py`, SHA-256
  `2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2`.
- Immutable 592-file profile corpus: SHA-256
  `c6d9bb025d829b0541286d3868adfd965501b24988f0898f6b23ecdd537c1c23`;
  the digest frames every sorted basename and file payload.
- Definitive `full_matrix_final.sbatch`: SHA-256
  `b1977478cdd2ee26c2cd607c4c5d6b6be3710c1cdb1eeb4e27365239801b185b`.
  A complete panel's strict timeout maximum is 104 minutes; the three-hour
  allocation leaves ample time for repeated parsing and local file handling.
- Strict analyzer: `analyze_matrix.py`, SHA-256
  `2beb8f85aaa3932c0ce66c3d49725a0a793362fa8e2e2cb54824e30d89241e79`.
- Current final smoke script: SHA-256
  `04c7ba140900901cdd961ea440a538af59f0af97eed6978c09ba247b444afdb0`.
  The first smoke submission, job `48883709`, found a wrapper continuation
  typo and produced zero rows. Corrected job `48883997` ran both paired panels:
  `ht_bridge` and `production_all` match gold on 541 and 12653.
  The definitive binary repeated the gate in job `48891559`.
- The final tableau-route smoke uses `smoke_tab_race_final.sbatch`; final-binary
  job `48891560` checked the current in-fragment witness 6246. The typed route
  (31.0035 s, 11,919 MB) and equivalent explicit bundle (31.0994 s,
  11,610 MB) both return all 322 gold subsumptions with no other difference.
  The preceding job `48887963` intentionally stopped after proving that 9635 is
  not a valid legacy-tableau witness anymore: no tableau worker spawned because
  its exact modern TInput carries the deliberate `inverse+number(SHIQ)` fence.
  The certified cardinality/bridge procedures, measured separately, own that
  fragment.
- Specialist job `48891561` proved typed/manual bundle identity for QO, SHOQ,
  cardinality, and bridge. Bridge closes 541 exactly. The other three isolated
  specialists time out on their former witnesses and stay measurement-only;
  the learned policy cannot select them.
- Local-name-collision gate `smoke_canonicalizer_412.sbatch`, SHA-256
  `32d6dcb72d9c91686fe21a25dcf60697067b6ffb3f1c34138807e7748620408c`,
  completed as job `48894378` before the definitive array dependency released.
- The definitive 592-ontology matrix writes only to `matrix-results-final3/`.
  Canonicalization-gated array `48894562` and its dependent strict analysis job
  `48895244` were submitted from empty result and failure directories. The
  latter cannot run unless all 592 array tasks finish successfully.

Every ontology's procedures run sequentially on one exclusive Intel Xeon Gold
6248 node. The ontology is copied to node-local storage. One Konclude run is
placed before the KM panel and the other after it; which thread count goes
first alternates by ontology. The 24 KM procedures rotate position by ontology,
so each occupies every warm/cold position 24 or 25 times. Every procedure has
the same 240 second and 20 GiB limits. Peak memory is the maximum sampled sum
of process-group RSS, checked every 40 ms and maxed with GNU time's peak.

Two still earlier partial arrays are retained on IBEX as smoke evidence only:
`matrix-results-smoke-fixed-order` and `matrix-results-smoke-rotated-13`.
They were cancelled after the matrix audit found fixed-order bias and missing
thread/absorption controls. No result from either partial run trains the tree.

## Exact Konclude expressivity

`engine/src/frontend/profile.rs` ports
`COntologyStructureSummary::calculateExpressiveness()` and the occurrence flags
set by `COntologyInspector` after preprocessing. The final code follows
Konclude's precedence exactly:

1. choose `AL`, `ALE`, or `ALC`;
2. contract `ALC` plus transitivity to `S`;
3. replace the base by `SR` for a complex role chain, otherwise append `H`;
4. append `O`, `I`, then one of `Q`, `N`, or `F`;
5. append `V`, `(D)`, and any remaining `+`.

The implementation walks parsed functional-syntax nodes rather than matching
keywords in source text. It also reproduces preprocessing effects that a direct
constructor count misses, including active-role reachability for nominal
domains, transitivity activation, inverse-partner role equivalence, retained
equivalence operands, and complex-chain suppression of `+`.

Validation compares `km profile` with the official Konclude binary on every
corpus ontology: **592 of 592 codes match, with zero mismatches and zero profile
errors**. The delta-debugged witnesses for the last three preprocessing cases
are committed as `ore_ont_7417-expressivity-witness.owl`,
`ore_ont_2313-expressivity-witness.owl`, and
`ore_ont_15516-expressivity-witness.owl`.

## Ontology statistics

`profile-table.csv` has one row per ontology. It includes the exact expressivity
flags and code, source byte and axiom counts, entity counts, constructor counts,
maximum expression depth/arity/cardinality/role-chain length, and normalized
clause-shape counts. `profile-summary.json` gives corpus distributions and the
20 largest ontologies under source bytes, logical axioms, and normalized
clauses.

The corpus contains 33 Konclude expressivity codes. Of 592 ontologies, 467 have
an EL-safe RBox and 125 do not. Median normalized size is 6,865 clauses; the
largest has 4,227,742. The largest source has 3,137,907 logical axioms and is
576,729,915 bytes. Across the corpus, the profiler counted 10,221,985,943
source bytes, 56,280,487 logical axioms, 137,111,445 concept expressions, and
72,477,784 normalized clauses. Of those clauses, 72,384,194 are Horn and
93,590 are disjunctive.

Source profiling now shares the frontend's first streaming parse pass and
releases its borrowed entity sets before normalisation. Detailed clause
statistics are requested by `km profile`; ordinary classification does not pay
for an extra full clause-vector scan because the deployable tree uses only
source and expressivity features.

## Procedure panel

The definitive matrix includes:

- current routing at 16, 8, and 1 worker threads;
- the complete trigger-absorption/Konclude-bridge stack at 16, 8, and 1 threads;
- plain CB at 16, 8, and 1 threads;
- direct absorbed CB and the sequential plain-then-absorbed portfolio;
- the certified EL portfolio and the legacy per-function CB strategy;
- general HT, QO certificate, SHOQ, cardinality, Konclude bridge, and DL-safe
  rules procedures;
- the historical label-caching tableau race, functional-cardinality, and the
  exact nominal-CB closure mode;
- forced-on and forced-off Sequoia definer ordering, alongside its normal
  structural auto-gate.

General HT, QO, SHOQ, first-class cardinality, historical tableau, and
functional-cardinality are measured but cannot become default tree leaves:
each has a documented corpus counterexample or lacks a complete procedure
contract. The analyzer admits trusted CB/EL procedures and output-preserving
variants for the SRIQ core. A hard semantic gate admits only exact nominal CB
for nominal/ABox inputs and only the certified rules procedure for supported
DL-safe rules; benchmark speed cannot relax either gate.

## Policy objective

`analyze_matrix.py` first requires an exact adjudicated classification. Wrong,
partial, timed-out, and memory-killed rows have infinite policy cost. For a
correct row it computes a strict Konclude envelope from the faster and the
lower-memory of the one- and 16-worker reference runs, then minimizes

`max(KM time / Konclude-best time, KM peak / Konclude-best peak)`.

A 2.5 percent mean-ratio term breaks ties. Each tree leaf first minimizes the
number of failures, then summed time/memory cost. The feature set contains only
source statistics and exact expressivity flags/codes; ontology identifiers and
post-route clause statistics are excluded. A deterministic five-fold audit
selects depth and minimum leaf size from a small declared grid. The emitted
Rust function is generated by `emit_rust_tree.py` and has no runtime machine
learning dependency.

Konclude's stale parse-failure gold for the proven-inconsistent SWRL ontologies
2669, 10906, and 15516 is replaced by the committed HermiT core adjudication,
as documented in `docs/CONTESTED-GOLD.md`.

## Reproduction

On IBEX, from the experiment directory:

```bash
sbatch full_matrix_final.sbatch
sbatch analyze_matrix.sbatch
```

After analysis, every oracle-best route with either time or memory more than
20 percent above the Konclude envelope is repeated three times by
`recheck_gaps.sbatch`. The KM runs retain `KM_TIMING` and frontend stage timing;
these traces support the required algorithm and complexity comparison rather
than attributing a one-run ratio to the reasoning kernel without evidence.

For production-route sweeps, submit `production_full_sweep.sbatch` with an
immutable `SWEEP_KM` and a unique `SWEEP_TAG`. A valid dataset has one JSON row
per ontology, the expected binary SHA on every row, and only `ok`, `timeout`,
`memout`, or `unsupported` terminal statuses. If a descendant allocation spike
kills the complete Slurm step before the watchdog checkpoints a row, rerun only
that array index. After the retry log contains an explicit `oom_kill event` or
`OUT_OF_MEMORY`, use `finalize_oom_rows.py`; it refuses to publish without that
evidence and computes the binary SHA itself. Never infer `memout` merely from a
fast job exit or a missing result file.
