# v1.4 baseline, ORE 1194 closure, and fresh 592 sweep

KM v1.3.0 (`f4738bc`, engine `5c64a02`, binary SHA-256
`cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d`)
completed 591 of the 592 ORE inputs and provides the optimization baseline.
The v1.4 candidate closes ORE 1194 and completes all 592 inputs.

Against every correct baseline completion in the retained 66-arm panel, the
v1.3 automatic route is strictly fastest on 410 of 589 comparable inputs,
strictly lowest-memory on 465, and wins both measures on 386. Three ORE inputs
have no correct baseline completion. These are per-ontology comparisons, not
aggregate means.

No retained baseline solves ORE 1194 within the common 240-second, 20-GiB
contract. The source is a nominal-free SRIQ ontology with 221,086 complex class
assertions over 18,055 individuals and no role assertions. Its source profile
passes the disjoint-union ABox candidate screen. A complete full-ontology
consistency decision would therefore authorize classification of the TBox-only
view without repeating the ABox in every taxonomy query.

`ibex_1194_consistency_projection.sbatch` measures the already certified v9
prototype with 3, 60, and 240 second consistency budgets. This is a diagnostic,
not a release result: it establishes whether the exact global check can close
the missing ontology before further implementation work.
The prototype binary is bound to its colocated `km.sha256` receipt
(`b21eda4b...`); the earlier narrative hash in the v9 experiment README was
superseded before the retained panel ran and is not used here.

`ibex_1194_existing_cb_curve.sbatch` separately measures the exact shipped
v1.3 nominal CB method at 1, 2, 3, and 4 threads under an extended 600-second
diagnostic limit. It preserves the existing calculus and route. The run records
whether the blocker is memory, throughput, or both after the latest shared-base
and compact-index implementations.

## Diagnostic result

Projection job `51108146` declined at every budget. Converting the 1,062,240
clauses to the hypertableau view alone took 225–233 seconds and drove process
RSS to 18.9–19.3 GiB, so this prototype is neither a closure nor a competitive
route for ORE 1194.

The first manual CB job (`51108662`) was invalid as a throughput curve: manual
routing omitted the automatic route's profile-derived `KM_COMP_IND_BITS=15`,
so each arm failed during setup at the packed `f(o)` representability guard.
The corrected jobs set the lossless layout explicitly. Four workers reached
23.26 GiB in 42.45 seconds and failed the 22-GiB diagnostic guard. Query batches
of one and eight did not bound that state: jobs `51111937` and `51111938`
reached 23.21 and 23.15 GiB in 24.44 and 23.39 seconds. This rules out an
unflushed message queue as the dominant memory source.

One-, two-, and three-worker corrected runs all remained in exact CB saturation
after the 240-second release contract. They were cancelled after crossing the
contract because an eventual extended-limit result could not qualify. Thus a
thread-count or existing query-batch routing change alone does not close 1194.
Three workers are the measured memory-feasible optimization point; further
work should reduce the persistent per-worker nominal ground-context state or
the established role-bridge closure cost. These are incremental improvements
to the existing exact CB method and do not require a new route.

## Rejected adaptive `pushed_pred` representation

An exact adaptive sparse-vector/bitmap replacement for each predecessor
edge's `HashSet<u32>` reduced memory but also reduced saturation throughput.
The change was representation-only and passed its focused membership tests and
all 15 `pred_` library tests. It did not close ORE 1194.

The initial zero-query one-worker diagnostic reached the 18-GiB internal guard
in 95.16 seconds at 17,310,044 KiB process RSS, compared with 85.18 seconds and
17,606,620 KiB for v1.3. Because a lower allocation rate can delay a memory
guard without increasing useful work, job `51115401` ran both binaries
sequentially on `cn604-15` with equal 40-second engine budgets. It measured
10,646,160 KiB for the adaptive candidate and 10,779,540 KiB for v1.3, but the
forced worker termination prevented final progress counters.

Job `51115947` therefore reversed arm order on the same node and enabled only
the compact `KM_PROF` counter. With equal 35-second engine budgets, the
candidate processed 10.82 million messages at 10,739,720 KiB, while v1.3
processed 11.74 million at 11,356,820 KiB. The candidate saved 617,100 KiB but
processed 7.8% fewer messages. This fails the combined time, memory, and
coverage objective, so the implementation was reverted rather than retained
as a slower default. The reproducible Slurm scripts are
`ibex_1194_zero_query_paired_mem.sbatch` and
`ibex_1194_zero_query_paired_progress.sbatch`.

## Existing-route existential-witness projection

The full source has 221,086 ABox axioms, all of them
`ClassAssertion(ObjectSomeValuesFrom(RO_0002200 C) a)`. There are no role,
negative-role, data, equality, inequality, key, rule, nominal, or universal-role
ABox couplings. Outside those assertions, `RO_0002200` occurs only in
`RO_0002200 o BFO_0000051 <= RO_0002200`.

This admits a fail-closed exact source certificate. For every assertion, take a
pointed model of its named filler `C`, add a fresh root for its individual, add
the `RO_0002200` witness edge, and close that role under the admitted chain.
The assertion role is otherwise unread by the TBox and RBox, so the construction
preserves each component model. The full ABox is consistent exactly when all
recorded fillers are satisfiable. The existing disjoint-union theorem then
proves that omitting the ABox preserves the public TBox taxonomy.

Job `51116626` measured that projected TBox with the exact v1.3 binary. The
ordinary automatic router selected `production_all` and completed in 228.67
seconds at 13,907,060 KiB, with `consistent=true`, no unsatisfiable classes,
`dropped=0`, and a 407,439,580-byte classification. Its exact TBox input SHA-256
is `31e6c1893e143e7b356358de52e29c21336229af03bc0ae706da8a9717493903`.
This is evidence that an existing KM method can close the case; the stripped
input alone is not a full-ontology result.

The v1.4 candidate implements the certificate in the parsed frontend, records
every filler through the existing asserted-class channel, projects the ABox,
and selects the existing complete TBox route. Publication fails closed if the
worker drops any clause. The final output mapper already turns an unsatisfiable
asserted class into a full-ontology inconsistency. Focused tests admit the exact
shape, reject TBox role use, reversed chains, changed chain heads, mixed roles,
and complex fillers, and exercise both consistent and inconsistent synthetic
ontologies. `ibex_1194_existential_abox_candidate.sbatch` is the authoritative
full-source validation; no 592/592 claim is made until that run succeeds.

The first full-source candidate run, job `51117586`, completed in 227.92
seconds at 15,764,384 KiB, but the mandatory set comparison in job `51117752`
caught 36 missing taxonomy pairs. There were no candidate-only pairs. The
projected frontend had accidentally disabled the existing TBox bottom prepass
because that prepass was shared with a broader ABox-elision optimization. It
therefore handed 14 fewer clauses to `production_all` than the independently
stripped reference. This run does not count as a closure.

The correction retains the bottom prepass for this exact projection. A focused
regression test now requires the projected source to produce exactly the same
clause and RBox payload as an independently ABox-stripped source containing a
bottom-propagating TBox. The rebuilt full-source run must also have zero pairs
on both sides of the comparison before ORE 1194 can be counted as solved.

Corrected full-source job `51118250` met that gate. It selected
`production_all`, handed all 966,310 clauses to the existing method, and
completed in 223.40 seconds at 15,977,744 KiB with `consistent=true`, no
unsatisfiable classes, and `dropped=0`. Its 407,439,580-byte output has SHA-256
`37abb42c139d5f5658ab8138834cda8cef4d29693e9abb82206f380d7ac44ffe`, exactly
the independently stripped reference hash. Job `51118460` additionally sorted
and compared all 3,141,651 full-IRI subsumption pairs and found
`candidate_only=0` and `reference_only=0`.

This establishes a targeted exact completion for the former residual using
the existing `production_all` method plus certified frontend projection. A
fresh full-corpus sweep remains required before reporting the automatic route
as 592/592, because that sweep is the regression gate for the other 591
ontologies.

The first final-source sweep, job `51118704` plus CPU-correct resume job
`51119620`, produced 592 results, checkpoints, and profiles with no temporary
files. The other 591 ontologies retained their established outcomes, but 1194
hit the common process-tree guard at 20,483.78 MiB after 69.54 seconds. This
does not invalidate the exact output comparison; it means the route did not
yet satisfy the 20-GiB release contract.

Per-process telemetry then measured a 22,439,056-KiB diagnostic tree peak. At
that instant the certified bridge worker held 18,463,380 KiB and its concurrent
exact CB fallback held 3,937,696 KiB; the supervisor held only 37,980 KiB. The
failed allocator-trim experiment and telemetry show that live duplicate
reasoner states, not retained frontend pages, caused the excess. The candidate
therefore schedules this already certified bridge before allocating the
unchanged CB fallback. A bridge defer still starts CB, so this is a scheduling
change only. It must pass the same process-tree watchdog before it counts.

## Incremental obligation propagation

A 90-GiB, five-hour control (job `51161963`) established that ORE 1194 was not
memory-bound. It timed out after 5:00:03 at 14,423,644 KiB RSS with 12,684,606
nodes, 26,730,429 obligations, 106,569,891 matches, and 1,757,473 obligations
still pending. Only three outer reasoning steps completed. Increasing the
resource limits therefore did not close the ontology.

The hypertableau now exposes each newly allocated existential witness to Horn
propagation before it scans the next sibling obligation. A stronger witness can
therefore discharge a weaker obligation immediately instead of allocating a
second node. This changes the fair schedule, not the monotone fixpoint. The
automatic router enables it only for the existing
`existential_witness_abox_candidate` profile. Default-route job `51169929`
completed ORE 1194 in 172.84 seconds at 16,464,308 KiB; two repeated runs
completed in 119.42 and 88.36 seconds at about 19.28 GB.

The completed taxonomy contains 3,141,659 subsumptions and no unsatisfiable
classes. Relative to the earlier 3,141,656-pair result, it adds exactly three
pairs and removes none. All three follow by transitivity through the already
established class
`CL_0000066-BFO_0000052-UBERON_0002185-BFO_0000050-BFO_0000052-9be1e5facfab0c0bb46587a82af23482`:
each source was already below that class, and that class was already below
`_lower_airway_obstruction-BFO_0000050`. ORE 1194 has no stored Konclude gold,
so this explicit two-hop witness, the exact set difference, and a focused
source-closure regression test form the correctness evidence. Clean-source
jobs `51171911`–`51171913` passed the final targeted release gates.

## Fresh automatic-route sweep

Array job `51171933` ran the clean candidate binary
`339511404d1ac015c61ab7b6a03687aeb0db72a6104a0aff9961983597c320e1`
on Intel Xeon Gold 6248 nodes. The source archive SHA-256 is
`affa892f8e51a06f1dc89358cc1389dfb455b0d5413cac6855b0557852ed83a6`.
All 592 tasks used only `KM_ROUTE=auto`.

The fail-closed audit found 592 results, 592 byte-identical checkpoints, 592
profiles, and no temporary files. Every result has status `ok`: 588 match the
retained signatures, 2669 and 15516 retain their independently adjudicated
inconsistency results, and the no-gold cases 10860 and 1194 retain their
independent certificates. ORE 1194 completed in 159.0527 seconds at 18,610.37
MiB process-tree RSS. Its local-name benchmark signature contains 3,141,651
pairs; the full-IRI result contains 3,141,659 because eight pairs collapse
under the benchmark's documented local-name canonicalization.

Across the 592 KM completions, mean and median wall time are 1.7798 and 0.1588
seconds. Mean and median peak process-tree RSS are 227.64 and 27.31 MiB. Against
the adjudicated per-ontology baseline ledger, KM is strictly fastest on 412 of
589 comparable inputs, strictly lowest-memory on 471, and wins both measures
on 389. Three inputs have no correct baseline completion. The remaining 177
time and 118 memory deficits are the active v1.4 optimization set, so the
stronger per-ontology speed and memory objective is not yet achieved. The
complete ledger is `v14-fresh-per-ontology.tsv`; its generator preserves the
collision-safe and independently adjudicated targets in
`v13-per-ontology-targets.tsv`.
