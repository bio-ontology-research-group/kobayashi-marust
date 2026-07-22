# Reproduced ORE routes, correctness, and performance

This directory joins the accepted source-bound KM route confirmations with
Konclude, HermiT, and ELK measurements for all 592 ORE ontologies. The main
artifact is
[`ontology-route-performance.tsv`](ontology-route-performance.tsv). It has one
row per ontology and records:

- the accepted KM route, command, environment, source revision, binary, wall
  time, peak RSS, taxonomy hash, and evidence record;
- Konclude, HermiT, and ELK status, wall time, peak RSS, binary, signature, and
  evidence;
- separate empirical `sound` and `complete` fields for every reasoner; and
- the evidence basis used for each correctness judgment.

The table was built by IBEX Slurm job `49284022` under a 240 second and 20 GiB
per-reasoner limit. The successful job ran only the metadata aggregator. It did
not rerun a reasoner. The accepted reasoner executions remain the hash-pinned
records cited by each TSV row.

## Headline results

Average and median performance use only rows with `status=ok`, so the metric
population appears beside every row. The KM and paired Konclude rows come from
the current source-bound full-IRI confirmation. HermiT and ELK come from the
repaired frozen external-baseline matrix on the same Intel Xeon Gold 6248 CPU
model and benchmark limits, but not the same Slurm job.

| reasoner and measurement set | sound + complete / 592 | metric rows | wall mean s | wall median s | peak mean MB | peak median MB |
|---|---:|---:|---:|---:|---:|---:|
| **KM, accepted reproduced routes** | **589** | 589 | 5.366 | 0.234 | 691 | 38 |
| Konclude 16, current paired full-IRI references | 587 | 587 | 3.376 | 0.235 | 561 | 75 |
| HermiT, repaired frozen matrix | 551 | 556 | 12.953 | 1.759 | 1,369 | 741 |
| ELK, repaired frozen matrix | 531 | 590 | 1.968 | 0.821 | 602 | 347 |

The strict same-ontology comparison over the 587 current full-IRI pairs is:

| reasoner | wall mean s | wall median s | peak mean MB | peak median MB |
|---|---:|---:|---:|---:|
| KM | 5.384 | 0.234 | 693 | 38 |
| Konclude 16 | 3.376 | 0.235 | 561 | 75 |

KM therefore has nearly the same median wall time as Konclude on the paired
set and about half its median peak RSS. KM has the higher mean wall time and
mean peak RSS because several specialist accepted routes are expensive.

For reference, the repaired frozen Konclude-16 baseline has 588 successful
rows, mean and median wall times of 2.129 and 0.264 seconds, and mean and median
peak RSS of 738 and 245 MB. That row is retained in
[`route-performance-summary.json`](route-performance-summary.json), but the
paired current row is the fair comparison to the 587 current KM full-IRI rows.

## Soundness and completeness fields

These fields describe empirical named-class taxonomy correctness against the
cited oracle or adjudication. They are not a proof that a reasoner is sound or
complete for every OWL input.

- `yes` means the cited evidence establishes the property.
- `no` means the cited evidence refutes it.
- `unknown` means a result exists but the available evidence does not decide
  the property.
- `not_applicable` means there is no classification answer to assess. A
  timeout, memory limit, unsupported input, or execution error has
  `sound=not_applicable` and `complete=no`.

The resulting field counts are:

| reasoner | sound yes / no / unknown / N/A | complete yes / no / unknown | sound + complete yes |
|---|---:|---:|---:|
| KM | 589 / 1 / 0 / 2 | 589 / 2 / 1 | 589 |
| Konclude | 589 / 0 / 0 / 3 | 587 / 5 / 0 | 587 |
| HermiT | 551 / 5 / 0 / 36 | 552 / 40 / 0 | 551 |
| ELK | 581 / 6 / 3 / 2 | 531 / 58 / 3 | 531 |

The two adjudicated inconsistent ontologies, `2669` and `15516`, count as
sound and complete for KM, HermiT, and ELK because each reports inconsistency
and the independent contradiction evidence establishes that result. Konclude
reports them consistent after failing to account for the rule axioms, so its
answers are sound subsets under explosion but incomplete. The table also
applies the documented `11745` empty-local-name gold-loader correction and the
`13503` missing-unsatisfiable-class correction.

## Coverage and residual

KM has 587 exact current full-IRI matches and two independently adjudicated
inconsistent classifications. Three rows remain nonclaims:

- `4669`: a completed KM answer is refuted by targeted satisfiability checks,
  so `sound=no` and completeness remains unknown;
- `10860`: the ontology contains unsupported DL-safe rule atoms and has no
  authoritative complete oracle; and
- `1194`: no tested complete KM route stays within the 20 GiB limit.

## Provenance

The successful result receipt is
[`route-performance-receipt.json`](route-performance-receipt.json), and
[`result-files.sha256`](result-files.sha256) checks the three generated result
files. Important hashes are:

- accepted route ledger:
  `7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354`;
- repaired 592-file external-baseline manifest:
  `a3310200ba3ad26b19cddc0173df5be65541ff5246cfea9062325cb1f799b06f`;
- generated TSV:
  `ff508acc0d9501344408820284396e0b0d91310c0f9275e16ccb7ccfa6047d94`;
- aggregation driver:
  `2305f9dce5092c0855b4a3d8a02847d885283900ae6ab4099ed3024109efd2f1`;
  and
- aggregation program:
  `a76d1618dbfe54b567a87ae446317da68e96eb4db8612de8a49564fb8785d07a`.

The repaired raw baseline has 590 successful ELK rows and 556 successful
HermiT rows. These supersede the 579 and 545 pre-repair successful-row counts
in the earlier July 16 aggregate. The raw files are pinned by the manifest
above, and every TSV row records the corresponding evidence-file hash.
