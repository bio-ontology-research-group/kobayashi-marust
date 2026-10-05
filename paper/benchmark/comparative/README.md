# Comparative benchmark harness

This directory measures classification, source-ontology updates, and one
subset-minimal justification against the same frozen workloads. It compares KM,
RustDL, Konclude, HermiT, JFact, Openllet, ELK, Whelk, MORe, and Sequoia.

The v1.4.5 evidence directory is
[`results/benchmarks/2026-10-04-v1.4.5-comparative`](../../../results/benchmarks/2026-10-04-v1.4.5-comparative).
Its `workload-protocol.json`, `workload-selection.json`, and
`classification-inputs.json` define the workload.
`run-set-global-dependency.json` selects the current certified KM candidate and
the independently preserved baseline runs. `global-dependency-rerun-submissions.json`,
`global-dependency-audit-submissions.json`, and
`global-dependency-validation/global-dependency-render-submissions.json` identify
the selected measurement, audit, and report jobs. Earlier run sets remain
historical evidence.
Job submissions and immutable worker snapshots identify the measured code.
`classification-scheduling-override.json` and
`benchmark-concurrency-adjustment.json` record increases in concurrent array
tasks; per-measurement CPU, time, and memory limits stayed unchanged.
`CURRENT-STATE.json` tracks work in progress; it is not a release certificate.

## Workload and limits

Classification retains all 1,920 original inputs, including invalid inputs.
Updates and justifications use 80 source-hash-selected ontologies, stratified by
source size. Selection precedes measurements; failed references and preparation
steps never cause an easier replacement ontology to be selected.

Each classification, update revision, or justification generation receives one
CPU, 240 seconds, and 20 GiB for the process tree. Independent justification
verification receives a separate budget. Preparation and syntax conversion have
their own recorded limits and costs. Linux `/proc`, GNU `/usr/bin/time`, Python
3.9 or later, and Java with `javac --release 11` are required. Runtime binaries,
JARs, compiled helper classes, source files, and outputs are hash-bound in the
receipts. Sequoia's inventory also pins its runtime JARs.

Updates have five revisions: original, one logical-axiom deletion, restoration,
a bounded batch deletion, and restoration. Three repetitions compare fresh
processes with retained sessions where supported. Declarations, annotations,
and anonymous-individual identity are preserved and checked after serialization.
Retained sessions do not by themselves establish internal incremental reuse.
KM's actual reuse receipts remain in the report; other unexposed reuse is unknown.

Justification queries come from a frozen HermiT reference. Up to three inferred
named subclass queries and their source-bound STAR modules are shared by all
reasoners. Each query has three repetitions. Native explanation APIs are used
where available; other interfaces use an explicitly recorded deletion adapter.
A different reasoner verifies source membership, entailment, and every
single-axiom deletion. MORe additionally needs separately measured consistency
evidence for its module because its classification interface reports unknown
consistency. Unsupported baseline features remain failures; no source axioms are
silently dropped to improve coverage.

## Measurement, audit, and reporting

`run_*` scripts prepare inputs or invoke measurements. Measurement scripts keep
raw statuses and outputs. `executed_unvalidated` means only that a process
produced output; it is not a correctness result.

`audit_classification_panel.py` checks source/artifact/output bindings and full-IRI
taxonomies before pairwise comparison. `audit_updates.py` checks every revision,
including fresh-versus-retained, independent-reference, and repetition comparisons.
`audit_justification_panel.py` checks each frozen case and its independent proof
receipt. Unknown consistency remains conditional and never becomes full agreement.

The `report_*` scripts retain the full workload denominator and all failure
categories. Paired cost summaries use identical cases with full agreement, or
independently verified justifications on both sides. Initialization is separate
from update phases. `report_preparation.py` preserves shared preparation costs,
source/module sizes, conversion costs, and the extra MORe consistency checks.
Costs are not silently amortized across repetitions.

After the selected measurements terminate, run the audit and report scripts
using the recorded submission files in the evidence directory. Each script's
arguments identify the measurement root, audit job, and explicit run set. Keep
new runs in new directories; do not overwrite raw receipts or immutable worker
snapshots. On IBEX, parsing, canonical closure, measurements, and tests run in
Slurm allocations, not on login nodes.

The v3 classification and update audits supersede v2 after two serializer
normalization corrections: exclude `owl:Nothing` itself from the list of
unsatisfiable source classes, and recognize serialized `owl:Thing` subsumption
by `owl:Nothing` as inconsistency. The original measurements and v2 audit
outputs are preserved. The v3 submission receipts and source manifest identify
the replacement audits and reports; the justification audit is unaffected.

The retained Konclude v2 measurement then makes the default plain-literal
datatype explicit in OWLlink requests. A paired synthetic and real-ontology
test found that Konclude's DOM parser omitted the datatype default used by its
file parser. OWLAPI exact-axiom checks confirm that the explicit serialization
preserves the input. `run-set-literals.json` selects the replacement retained
panel; the v4 update audit uses that run set. Earlier retained measurements
remain available but are superseded for the final comparison.

The combined candidate supersedes the cancellation-only KM measurements after
additional datatype, nominal-dependency, and universal-propagation fixes. The
v4 classification and v5 update audits use `run-set-combined.json`; their
normalizer gives exact source IRIs precedence over prefix expansion. The v4
justification audit uses its own complete immutable helper package. The v2
preparation report selects the combined run set while retaining the unchanged
preparation measurements. Package and selection repair receipts preserve the
superseded job identities.

The current global-dependency candidate supersedes the combined and cached-model
candidates. The cached-model fixes recover missing classification consequences;
the later retained-EL fix preserves global superclass consequences when replacing
a component. All three KM panels are measured again for this candidate using
`run-set-global-dependency.json`; the frozen baseline runs and preparation inputs
remain unchanged. The corresponding classification v4, update v5, justification
v4, and preparation v2 reports use this same run set. Earlier timings are not
substituted for current candidate measurements. Validation and source manifests
are under `global-dependency-validation/` in the evidence directory.

The readable report is generated from the four JSON reports:

```bash
python3 paper/benchmark/comparative/render_report.py \
  classification-report.json updates-report.json justification-report.json \
  benchmark-report.md --preparation preparation-report.json
```

The renderer rejects mixed run sets by default. When a replacement affects only
one panel, `--run-set final-selection.json` requires every panel to match all
selected runs that it consumes, including the shared inventory. The report
keeps the historical input-report hashes and lists the final measurement
selection; it never rewrites an older report's receipts. Its output
does not claim release approval. Review disagreements and missing evidence before
publishing. Release also requires the exact-source Rust, Java/plugin, and four
production Lean gates, including the axiom audit and a matching tagged source.

## Harness checks

From a repository checkout on a compute host:

```bash
PYTHONPATH=paper/benchmark/comparative:oracle/ore \
  python3 -m unittest discover -s paper/benchmark/comparative -p 'test_*.py' -v
python3 oracle/ore/test_tree_watchdog.py
```

The taxonomy and justification tests require the small real-output fixtures in
the evidence directory. The standalone watchdog suite is an executable test
script, not a unittest-discovery module. Its frozen-runner fixture is
`results/benchmarks/2026-07-15-routing/bench_one_matrix_frozen.py`.
