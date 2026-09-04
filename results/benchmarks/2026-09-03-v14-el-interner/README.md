# Shared-symbol EL interner panel

This panel evaluates commit `2ffc48126a8d154eba7a8908daa241f5c3cabdc6`,
which stores each interned EL symbol once behind `Arc<str>` instead of once in
the lookup map and once in the reverse-name vector. The representation change
does not alter completion rules or their scheduling.

## Exact artifacts

- Candidate source archive SHA-256:
  `76d509ffd0281c3c242a4800eb9c838e04cfc2a35785c7405ab6a40849db30a8`
- Candidate binary SHA-256:
  `5b3350b718c593dda5854b5f3df9ced72c7eb8ce76ba41e5d26dac0da8a8955e`
- Control binary SHA-256:
  `c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d`
- Build job: `51298207`, with `BUILD_COMPLETE` and deployment checks passing
- Paired array job: `51298342`
- Remote evidence root:
  `/ibex/scratch/hohndor/km/v14-el-interner-shared-20260903`

Every retained run used the automatic route, selected `elc`, ran on an Intel
Xeon Gold 6248 node with 16 assigned CPUs, and had a 480 s timeout and 20 GiB
reasoner cap. Control and candidate alternated within each five-repeat group.
The runner required `status=ok`, `verdict=match`, the expected binary digest,
a valid checkpoint, and the `elc` route before publishing a result.

## Result

All 80 retained runs completed and matched Konclude's signature. Across the 40
paired repeats, the candidate/control geometric-mean ratio was `0.979205` for
wall time and `0.997028` for peak memory, corresponding to 2.08% lower wall
time and 0.30% lower peak memory. The per-ontology paired medians are in
`paired-summary.tsv`.

The small per-ontology ratios straddle one because these classifications take
roughly 2.5--4.6 seconds and ran on paired, model-identical nodes rather than
the same physical node. The representation change is retained because it
removes duplicate symbol allocations, preserves every answer, and improves
both aggregate measurements. It does not by itself close the EL wall-time
residuals against ELK.

## Harness correction

The initial ontology list incorrectly included `ore_ont_11745.owl`. Its first
six tasks correctly matched the reference but selected `cb_plain16`, causing
the panel's fail-closed `selected_route_trace == elc` assertion to reject them.
The remaining four tasks for that ontology were cancelled, and 11745 is not
included in the 80-run result or aggregate. The corrected reproducibility list
contains exactly these eight EL-routed ontologies: 6722, 7340, 7868, 12087,
12387, 13224, 15976, and 16596.

Raw JSON records, checkpoints, task logs, build log, source archive, and binary
remain under the remote evidence root. A local working copy of the raw records
and the fail-closed paired aggregator is retained under
`.work/artifacts/v14-el-interner-shared/` and is intentionally not committed.
