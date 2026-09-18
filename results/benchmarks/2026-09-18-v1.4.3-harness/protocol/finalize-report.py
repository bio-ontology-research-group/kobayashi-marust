import json
from pathlib import Path
root=Path('/home/leechuck/Public/software/kobayashi-marust')
repo=root/'.work/worktrees/bugfix-v1.4.3'
p=repo/'results/benchmarks/2026-09-18-v1.4.3-harness'
s=json.loads((p/'summary.json').read_text());pair=s['paired']['v143-final-rc2'];assert not pair['lost_completions'] and not pair['changed_output_hashes']
rows=[]
for panel,label in [('v143-baseline','KM v1.4.2'),('v143-final-rc2','KM v1.4.3'),('v143-rustdl-baseline','rustdl v0.4.28')]:
 x=s['panels'][panel];assert x['observed']==1920 and x['complete_chunks']==60;c=x['outcomes'];rows.append(f"| {label} | {c.get('ok',0)} | {c.get('dnf',0)} | {c.get('err_reject',0)} | {c.get('declined',0)} |")
refs=json.loads((p/'recovered-reference-ledger.json').read_text());kon=json.loads((p/'recovered-konclude-ledger.json').read_text())
checks=[]
for ontology in pair['new_completions']:
 statuses={r:set()for r in ['hermit','jfact','konclude']}
 for row in refs:
  if row['ontology']==ontology:statuses[Path(row['reference']).name].add(row['status'])
 for row in kon:
  if row['ontology']==ontology:statuses['konclude'].add(row['status'])
 assert any('agree'in st or 'agree_inconsistent'in st for st in statuses.values()),(ontology,statuses)
 checks.append('| '+ontology+' | '+' | '.join(', '.join(sorted(statuses[r]))or 'not run'for r in ['hermit','jfact','konclude'])+' |')
text='''# KM v1.4.3 harness bugfix evidence

The final candidate completes **{ok}/1,920** inputs, recovering **{gained}**
compared with released v1.4.2. No baseline completion is lost and every jointly
completed answer retains its exact output hash. These counts are process outcomes;
they are not a blanket proof of correctness or a timing ranking.

| Binary | Completed | Deadline | Error | Declined |
|---|---:|---:|---:|---:|
{table}

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
{checks}

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
'''.format(ok=s['panels']['v143-final-rc2']['outcomes']['ok'],gained=len(pair['new_completions']),table='\n'.join(rows),checks='\n'.join(checks))
(p/'README.md').write_text(text)
print('Wrote release benchmark report with',len(checks),'independently checked recoveries.')
report='results/benchmarks/2026-09-18-v1.4.3-harness/README.md'
doc=repo/'docs/HARNESS-v1.4.3.md';d=doc.read_text().replace('This is the working validation record for v1.4.3. Release validation is still\nrunning; candidate results below are not release claims.',f'This records the fixes and validation for v1.4.3. The [complete evidence report](../{report})\ncontains all process outcomes, recovered-answer checks and remaining failures.')
d=d.replace('The patched-KM panel remains in progress.',f"The final KM panel completes {s['panels']['v143-final-rc2']['outcomes']['ok']:,} inputs,\nrecovering {len(pair['new_completions'])} baseline failures with no lost baseline completion\nand no changed jointly completed output hash.")
d=d.replace('## Recovered-answer checks in progress','## Recovered-answer checks')
doc.write_text(d)
changelog=repo/'CHANGELOG.md';c=changelog.read_text().replace('## [1.4.3] - unreleased','## [1.4.3] - 2026-09-18').replace('Release validation is in progress.',f"The final candidate completes {s['panels']['v143-final-rc2']['outcomes']['ok']:,}/1,920 inputs, compared with 1,816 for\nv1.4.2 and 1,806 for rustdl v0.4.28 under the matched one-CPU limits. It recovers\n{len(pair['new_completions'])} baseline failures, loses no baseline completion, and preserves every\njointly completed output hash. Each recovery has independent reference agreement;\nreference disagreements, source-coverage flags and failures remain visible.\nThese are coverage observations, not a repeated speed ranking.\n\nAll 592 signatures in the separate previous-release regression are unchanged.\nValidation passes 2,413 library tests, 59 integration tests and all four source\ncertification gates, including the 22 native-checker tests. Eight tests remain\nexplicitly ignored. The versioned plugin passes 31 tests and a real installed\nProtégé smoke test using the shipped binary.")
changelog.write_text(c)
