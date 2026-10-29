# Context regime of the Sequoia ordering under nominals: measurements

Regime: `KM_SEQ_ORDER=context` (docs/PER-CONTEXT-ORDERING.md), auto-selected
in nominal mode. Binary: `engine/target/release/km` at commit 72160291
(snapshot `km.final` in the agent scratch directory). Machine: the shared
workstation (56 cores) with other agents' jobs running; the differential ran
with 4 threads next to the sequential ORE timing.

Tools:

- `gen_nomdata.py SEED OUT [--no-inverse]`: random OFN mixing nominals, data
  values, at-most restrictions, disjunctions and ABox assertions.
- `diff_run.py`: KM routes against cached HermiT answers.
- `diff_summary.py`: verdict counts and the reference verdict of every
  context-regime run that was not `ok`.
- `ore_time.sh`: sequential timing of the gated ORE inputs (300 s cap),
  keeping the sorted SUB/UNSAT/CONSISTENT lines.
- `ore_compare.py`: comparison with the 2026-10-28 baseline and the same-day
  unordered run.

Data:

- `ore-times-context.tsv`, `ore-times-unordered.tsv`: file, tag, rc,
  seconds, first route printed. `ore-compare.tsv`: per file, the 2026-10-28
  plain-Sequoia (h7) and unordered (sq1) times, today's context and
  unordered times, and whether the taxonomies agree.
- `engine-level.tsv`: `km engine` runs on 10874, 9800, 15655.
- `diff-*-context.tsv`: HermiT differential under the context regime
  (file, route, verdict, seconds, missing/extra subsumptions, missing/extra
  unsatisfiable classes, consistency mismatch). `diff-*-unordered.tsv`: the
  same files rerun with `KM_NO_SEQ_ORDER=1` where the context run was not
  `ok`.

Sets: `sorts` = engine/tests/fixtures/sorts_differential (11 files);
`fresh2` = gen_nomdata.py seeds 2000-2399 with `--no-inverse`;
`freshinv` = gen_nomdata.py seeds 1000-1099 (with inverse roles);
`sq` = the 300 ALCHIQ seeds of `.work/agent-assets/2026-10-28-scratch/sq/`
(no nominals and no data values, despite the description they were handed
over with; the `nominals` route forces nominal mode on them).

## Base context regime revalidation (commit a689c42b, binary `km.base`)

- `ore-individual-files-on-flag.tsv`: individuals/`on` flags of the 950 corpus
  files under 20 MB that mention individuals (`onflag.sh`, `classify_on.py`,
  `km ofn` with `KM_NOMINALS=1`, 60 s).
- `ore-regime-change-before.tsv` / `-after.tsv` / `-compare.tsv`: the 425 files
  with individuals and `on` false, `km.final` (regime 0) against `km.base`
  (base context regime), 300 s cap, the two streams run side by side.
- `ore-base-rule-9800-10874-15655.tsv`: the three cost files under `km.base`.
- `diff-*-base-rule.tsv`: HermiT differential under `km.base` (fresh2: first
  128 files only). `diff-sets-on-flag.tsv`: the flags of every seed.
