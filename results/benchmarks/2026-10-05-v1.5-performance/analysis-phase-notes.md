# Subject preparation and classification-message costs

The retained 13276 trace from job 53320659 contains 24,115 read-off records.
Their timers sum to 2.884 seconds of seeding, 44.789 seconds of search,
6.002 seconds of cache work and 0.180 seconds of label extraction. The
existing outer preparation timer attributes another 19.39 seconds to
classification-message analysis. The trace visits 13,151,589 other-node
labels and emits 261,169 messages across those model analyses. These are
instrumented diagnostics, not new release performance measurements.

The source shows several possible contributors to analysis cost: cloning the
node vector, walking and copying successor snapshots, constructing possible
subsumption states, building root/other-node messages, and applying messages
to classifier state. The possible-state collector can revisit the same concept
and reconstruct its sorted candidate list while the classifier state remains
immutable. The analyser also computes other-node visits more than once.
These are hypotheses for repeated work, not yet measured dominant costs.

The new observers use the existing `KM_BRIDGE_PHASE_TIMING` switch. They
separate snapshot preparation, analyser work and classifier delivery in the
bridge, then divide analyser work into seven phases. They read the clock and
write diagnostic output; no ontology, rule, queue, verdict or classification
message is changed. Timer groups are nested and must not be added together.
The added output can affect timing, so it cannot establish a speedup.

The three-case diagnostic uses unchanged inputs 13276, 13242 and 16680, the
pinned instrumented binary, one subject worker, 240 seconds, 20 GiB and one
CPU. Completed classifications are independently audited against the pinned
full-DL references. The inventory explicitly leaves exact-source production
certification pending for this diagnostic binary; the live full-corpus sweep
continues with its original certified-source binary.

`summarize_analysis_phases.py` checks the inventory, source, runner, measurement
and stderr hashes before aggregating timers. It retains failures and audit
outcomes. Optimizing a suspected repeated operation requires evidence from
these phases, preservation tests and an independently audited performance
comparison before any release claim.

The release build succeeded, and all 152 focused classification-analyser tests
passed both with timing enabled and disabled. All 624 recorded Rust source and
build-input hashes were rechecked after compilation. IBEX job 53331735 runs
the three-case diagnostic. Job 53329459 remains the independent full sweep;
neither job is restarted or replaced by this diagnostic.

Job 53331735 finished all three classifications with independent agreement,
but did not retain the worker's detailed timers. The orchestrator forwards
worker stderr only when `KM_HT_STATS` or `KM_HT_TRACE` is set; the first
diagnostic omitted both. Its outer timing and answer records remain preserved,
but it is explicitly unusable for the intended phase breakdown.

The summarizer now reports `usable_for_phase_diagnosis` separately from job
completion and lists cases missing timer groups. The retained first run is a
real negative check for this distinction: complete, three verified answers,
and unusable timing evidence. Job 53332023 uses a separate v2 runner with
`KM_HT_STATS=1`, the same immutable binary, inputs, limits and answer audits.
The first job is terminal; no live job was restarted.
