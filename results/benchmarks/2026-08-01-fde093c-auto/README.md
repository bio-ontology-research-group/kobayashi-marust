# Automatic ORE sweep after exact-role NF4 indexing

This source-bound production sweep measures one command, `km classify`, over
all 592 ORE 2015 ontologies. Routing is selected from ontology features without
consulting expected answers.

## Provenance

- Reasoner source commit: `fde093c`
- Documentation commit at publication: `df0513b` (no reasoner-code changes)
- Cluster-native build job: `49793038`
- IBEX binary SHA-256:
  `0aa78e92d327c2e73570243388e43347abb199d1bef9d461c94302a1d5eff20b`
- One-task end-to-end gate: `49793193`
- Resumable 592-task array: `49793194`
- Streaming full-IRI 4669 row: `49794816_157`
- Independent 4669 pair-stream oracle: `49795051`
- Remote evidence root:
  `/ibex/scratch/hohndor/km/release-fde093c-auto-20260801`
- Contract: 240 seconds, 20 GiB reasoner process-tree RSS, 16 CPUs, Intel
  Xeon Gold 6248 nodes

The workstation build is not ABI-compatible with IBEX because it requires
GLIBC 2.39. Array `49792957` was cancelled immediately after that provenance
gate failed. Job `49793038` rebuilt the exact git archive on an IBEX compute
node; `km routes` and the one-task production gate both passed before the full
array was submitted.

## Result

| measure | value |
|---|---:|
| terminal rows | 592 |
| `status=ok` | 591 |
| error | 1: ontology 1194 |
| retained Konclude full-IRI matches | 587 |
| independently adjudicated results | 4: 2669, 4669, 10860, 15516 |
| mean / median wall over OK rows | 6.6849 s / 0.2788 s |
| mean / median peak RSS over OK rows | 833.30 MiB / 45.18 MiB |

Every row has the same binary checksum, a unique ontology and array index, a
terminal checkpoint, and a nonempty automatic route trace. The complete TSV is
[`automatic-results.tsv`](automatic-results.tsv).

[`verified-route-capabilities.tsv`](verified-route-capabilities.tsv) is the
long-form capability ledger requested for route restoration. It has one row
for every ontology and KM procedure arm that completed with an accepted result
in the corrected v0.2.0 592-by-55 uniform panel, plus the current independently
verified 4669 automatic route. It contains 22,469 rows and its route union
covers 591 ontologies. Each row retains the tested source revision, binary
hash, result digest, resource measurements, correctness basis, and Slurm job.
The `arm` column distinguishes separately tested procedures that share a
logical route name. The generating script validates all 592 panel files,
requires 55 distinct arms in each, rejects ontology 1194, and requires the
union to contain exactly 591 ontologies.

An exact row-by-row comparison with the v0.2.1 release sweep found zero changes
in status, verdict, consistency, or semantic signature. The NF4 index therefore
preserves every demonstrated result. Ontology 1194 still selects `nominals` and
fails closed without a taxonomy.

## Ontology 4669 harness treatment

KM completed 4669 in 69.6804 seconds at 5,686.5 MiB. The generic local-name
postprocessor reached 79.9 GiB RSS after reasoning had completed, so it was
cancelled. The streaming full-IRI runner used 483.9 MiB for fingerprinting and
reproduced the retained taxonomy's SCC digest
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`:
846,306 pairs and zero unsatisfiable names. The independent pair-stream oracle
also reproduced digest
`d02decbafe66d8a9f1afaf7385785b6937fe46c1f288a33113c83c2bbe805b96`.
The published row records both encodings and the separate job identities.

## 1194 optimization gate

The exact-role Sub-NF4 index reduced the 1194 candidate's Sub-NF4 probes from
about 3.32 billion to 774,848,772, but the candidate still timed out after
245.40 seconds with zero output. A separately tested propagation-dedup candidate
reduced Edge-NF4 visits from 2,086,666,580 to 1,595,884,325 and peak RSS from
11,101,160 to 10,379,944 KiB, but also timed out after 245.33 seconds. Its
registration duplication rate was only 10.5%, so hash overhead consumed the
saved scans; that candidate was not merged.
