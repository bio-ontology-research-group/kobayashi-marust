# Justification comparison rendering

`render_justification_comparison.py` reads the frozen task matrix, raw results,
independent audit and OWLAPI normalized-support table. It never changes them.
`justification-comparison-config.json` names the two current baseline roots.
After their audits finish, deploy the renderer plus `audit_justification_main.py`
into a separate reporting directory and run through Slurm after workspace
preflight:

```
python3 render_justification_comparison.py justification-comparison-config.json report
```

The default required baseline is 300 tasks: 240 original, 60 ZFA supplement.
It expands these into 9,180 attempted extractions, including 1,530 warmups and
7,650 measured repetitions. Missing invocations are explicit rows. A terminal
extraction, completed task, independently verified support, and comparable
timing are separate properties. Preparation failures remain in panel.tsv:
MRO is pure DL; TO and UBERON contain rules and remain extension cases.

Outputs are comparison.md and TSV tables for every attempt, per-case dispersion,
coverage, paired wall-time ratios, preparation outcomes, artifact hashes,
runtime/source bindings, and integrity issues. Raw occurrence support counts
and distinct logical support counts are separate. Zero-support false answers
and inflated duplicate bounded outputs cannot generate timing wins. Timeouts
and memory censoring differ from unknown library enumeration. Internal Java
latencies remain diagnostic columns; comparisons use compatible end-to-end wall
times and retain the extraction mechanism and source track.

For final KM timing, add `km_final_sources` entries with the same schema as
`sources`. Their frozen tasks must contain exactly `km-native` and `km-common`
for every baseline query/source/track/repetition. Both manifest sets must match
and the extraction runner, common Java extractor and HermiT runtime hashes must
be identical. Final KM replaces baseline KM only in paired comparisons; raw
baseline and final rows remain available separately. Any missing final case or
protocol mismatch disables paired speed claims. Do not run final timing before
the parent release/certification gates pass.

Validation used the real completed first task with all300 frozen manifests.
The renderer retained all9,180 expected rows:33 terminal warmup extractions,
9,147 missing attempts, and zero eligible timing rows without normalization.
Separate, explicitly synthetic fixtures showed that a fast zero-support false
answer is rejected, two duplicate valid occurrences count as one logical support
and are ineligible at bound10, and a changed runtime receipt disables timing.
These renderer checks are not main benchmark performance evidence. Transient
fixtures/reports are in `.work/justification-renderer-check/` of the task worktree.

The configured final roots now exist for v1.4.2. Local validation against their
actual frozen manifests confirms all300 final cases align exactly with baseline
cases, adding1,800 KM attempts (1,500 measured). The combined audit matrix has
10,980 attempts,9,150 measured; baseline KM remains visible but final KM alone
enters peer ratios. Preparation outcomes are listed once, not recounted for the
version rerun. Markdown paired summaries require all five measured repetitions
per case before reporting a case ratio; incomplete cases stay in the denominator.
