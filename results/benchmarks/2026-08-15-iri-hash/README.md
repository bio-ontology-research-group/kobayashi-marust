# Taxonomy IRI hash-index evidence

Release candidate `bf54bc2` replaces the lookup-only ordered local-name index
used during grouped JSON output mapping with a hash index. The sorted IRI table
and ordered taxonomy rows remain authoritative for serialization.

## Full ORE gate

Order-balanced same-node Slurm job `50535110` compared released v0.2.29 binary
`c5b85fea05cae73db5f66ec3a0b86c8439fd58ec207a612b07e85c91d08081dd`
with candidate binary
`1da5c66a96425cba2fe87cd208c1f58b1cc363fc85c9a69253f79190d3d632a1`.
The job produced 1,184 validated result rows and 1,184 checkpoints for 592
ontologies. All 592 pair tasks completed without a harness failure.

Both arms contain 591 successful classifications and one fail-closed ORE1194
error. Comparison found zero differences in status, verdict, consistency,
selected route, or full-IRI signature.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---:|---:|---:|---:|
| v0.2.29 baseline | 3.524409 | 0.1874 | 424.0097 | 35.38 |
| candidate | 3.479964 | 0.1617 | 423.7003 | 34.41 |
| candidate minus baseline | -0.044445 | -0.0257 | -0.3095 | -0.97 |

Paired wall differences sum to -26.267 seconds across the 591 successful
ontologies. Candidate wall is lower on 321 rows and higher on 262; candidate
RSS is lower on 271 rows and higher on 246, with 74 exact RSS ties.

## Node-local output measurements

Job `50534930` wrote each full classification to node-local `/tmp`, parsed the
JSON, compared complete output bytes, and retained only timings and SHA-256
receipts. This removes shared-filesystem and canonicalizer contention from the
dense-taxonomy measurement.

| ontology | baseline s | candidate s | baseline peak KiB | candidate peak KiB |
|---|---:|---:|---:|---:|
| ORE10689 | 34.49 | 31.83 | 1,682,016 | 1,680,236 |
| ORE868 | 34.80 | 32.38 | 1,680,560 | 1,679,924 |
| ORE1012 | 34.17 | 33.49 | 3,104,140 | 3,102,660 |

For each ontology, baseline and candidate JSON SHA-256 values are identical.
The complete release test suite passes 1,994 library tests with eight ignored
tests and every integration test, including `issue_3_soundness`.
