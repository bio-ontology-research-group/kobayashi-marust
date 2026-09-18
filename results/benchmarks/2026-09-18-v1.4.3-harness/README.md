# KM v1.4.3 harness bugfix evidence

The final candidate completes **1829/1,920** inputs, recovering **13**
compared with released v1.4.2. No baseline completion is lost and every jointly
completed answer retains its exact output hash. These counts are process outcomes;
they are not a blanket proof of correctness or a timing ranking.

| Binary | Completed | Deadline | Error | Declined |
|---|---:|---:|---:|---:|
| KM v1.4.2 | 1816 | 33 | 61 | 10 |
| KM v1.4.3 | 1829 | 79 | 2 | 10 |
| rustdl v0.4.28 | 1806 | 106 | 8 | 0 |

The corpus is the complete ORE 2015 sample (Zenodo 18578); the harness repository
supplies the protocol, not these ontology files. All inputs are pinned by SHA-256.
Harness commit: `7559c4543b270eb3a26cc88a6d4e837cffa0b84f`.
Each run uses one allocated Gold 6248 CPU, 20 GiB address space and a 240-second
external deadline. The stock `run-km-v140.sh` wrapper selects auto routing and
`KM140_BIN` identifies the actual binary. Resource budgets are identical across
the three primary panels. Scheduling and timing caveats are recorded in
`scheduling-amendment.json`; do not interpret the panels as repeated speed tests.

## Recovered-answer checks

| Ontology | HermiT | JFact | Konclude |
|---|---|---|---|
| ore_ont_10391 | agree | agree | not run |
| ore_ont_10754 | agree | consistency_disagreement | agree |
| ore_ont_11895 | agree | agree | not run |
| ore_ont_13526 | unverified | agree | not run |
| ore_ont_16371 | agree | consistency_disagreement | agree |
| ore_ont_16542 | unverified | agree | agree |
| ore_ont_1931 | agree | agree | not run |
| ore_ont_2837 | agree | agree | not run |
| ore_ont_3561 | agree | consistency_disagreement | agree |
| ore_ont_4410 | agree | agree | not run |
| ore_ont_5162 | unverified | unverified | agree |
| ore_ont_7517 | agree | agree | not run |
| ore_ont_9694 | unverified | unverified | agree |

`agree` compares full-IRI relations, the consistency verdict and unsatisfiable
classes. The Konclude comparisons expand its direct taxonomy using the pinned
harness normalizer and require empty special-class groups for these cases.
`unverified` retains a reference timeout or error; consult the receipt and stderr.
A reference disagreement is preserved even when two other reasoners agree.
No majority-vote proof is claimed.

## Regression and remaining limits

The separate 592-input, 16-CPU regression reproduces the previous release's
protocol: all 592 complete, 588 match retained gold, two retain known consistency
disagreements and two have no external gold. All 592 signatures match v1.4.2.
This is distinct from the one-CPU Michel-harness panel.

Of rustdl's 1,806 completions, 99 report incomplete reasoning and 431 report
dropped axioms; 480 have either flag. Of its 78 completions absent from the
v1.4.2 baseline, 65 have either flag. A flag does not prove an incorrect answer.
KM's field named `dropped` counts worker clauses and is not comparable to
rustdl's source-axiom omissions. The per-input audit is retained.

Timeout reporting alone is not a recovered completion. The baseline failure
ledger distinguishes internal deadlines, external deadlines, allocation failures,
unsupported inputs and an unidentified signal. Unsupported SWRL inputs and the
three inverse-role-chain inputs remain unsupported. The release does not add a
general tableau fallback or approximate unsupported syntax.

## Evidence layout and reproduction

- `panels/`: complete process rows, wrapper headers, host information and completion markers;
  recovered KM JSON outputs are gzip-compressed without altering their bytes.
- `references/`: independent classifier receipts, diagnostics and classifications.
- `gold-regression/`: all 592 candidate records and the previous release's table.
- `provenance/`: corpus, source, binary and validation identities.
- `protocol/`: scripts and inputs for staging, Slurm runs and diagnostics. Names
  identifying earlier candidates or forced HT are superseded experiments, not
  release settings. Use `v143-rc2.sbatch` for the final one-CPU panel.
- `superseded-rc1-summary.json` and `diagnostics/`: the earlier candidate's result
  and the initial 3215 timeout. `references/paired-3215` retains the complete
  ABBA replay. Replays do not replace any primary panel row.

Recompute the panel summary with `summarize.py`, putting the baseline first.
Use `compare_references.py` for HermiT/JFact and `compare_konclude.py` with
`--normalizer protocol/normalise.py` for Konclude. All programs accept the
retained paths; KM JSON may be compressed. The release validation asset binds
2,413 library tests, 59 integration tests, 22 native-checker tests within four
certification gates, eight explicitly ignored tests, and 31 plugin tests to
the recorded sources. The installed-plugin smoke test uses the shipped binary.
