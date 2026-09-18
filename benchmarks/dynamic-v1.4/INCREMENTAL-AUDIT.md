# Incremental result audit

`audit_incremental.py` audits complete source histories while streaming each
canonical signature. It never loads a complete taxonomy into memory. Run large
panels on a Slurm compute node. JSON and Markdown outputs are written from an
output filename stem.

```sh
python3 audit_incremental.py DRIVER_ROOT --scope controls --out controls-audit
python3 audit_incremental.py DRIVER_ROOT --scope all --out panel-controls-audit
python3 audit_incremental.py DRIVER_ROOT --phase measured --scope panel \
  --repetitions 5 --out measured-audit
```

The measured audit includes both warmup arms as well as the requested measured
repetitions. A pilot does not count as the complete release evaluation.

## Checks and evidence limits

The auditor derives expected cases from `inputs/controls.json` and the frozen
`incremental-panel.tsv`. It checks each state manifest, measurement status and
manifest hash, contiguous signature and timing revisions, exact COMPLETE marker,
and response receipts. It compares every session against its own fresh arm and
every arm against fresh HermiT; acceptance against two independent references
also requires HermiT and fresh JFact to agree. Disagreements are reported by
revision; no majority vote silently changes the reference.

For full `.sig` and `.sig.gz` files, the auditor streams exact bytes into SHA-256,
checks row structure and ordering, counts rows, and reads explicit consistency.
For `.sig.sha256` files, it checks the digest format and compares the producer's
hash of the complete canonical taxonomy. Such files are labelled
`producer_digest_only`: the auditor cannot independently check their row layout
or recover consistency. Analytic consistency controls therefore require full
signatures. Keep the full pilot artifacts and reproduce a full signature for
any mismatching digest; matching one sampled edge is not an adequate check.

Analytic controls check consistency at every revision and restoration of the
initial taxonomy at every even round-trip revision. KM receipt summaries
separate `el_delta`, `exact_rebuild`, route changes, retained state counts and
actual reuse flags. `retained_backend: true` alone does not establish retained
inferences. Receipt claims remain instrumentation evidence, not an independent
proof of internal work reuse.

JSON retains measurement provenance, runtime and source hashes, manifests,
per-signature hashes, timing interval names, and auditor source/job/host identity.
It reports `full_scope_verified` separately from process success. The auditor
returns normally after writing a failure report; callers must inspect this
field and the issue list. No cross-interface speedup is calculated: KM source
request/response and Java inference-only intervals contain different work.

## Frozen baseline controls: failures found

Remote root: `/ibex/scratch/hohndor/km/dynamic-benchmark-20260917`.
Controls live under `incremental-driver-v2/panel-pilot/`. Slurm audits 51981218
and 51981232 completed successfully; evidence is retained as
`controls-audit-v1.{json,md}` and `controls-audit-v2.{json,md}`. All 48 reasoner
arms reported process status `ok`; that did **not** establish correctness.
Fresh HermiT and JFact agree on all six controls.

* KM emits unresolved names on several controls, for example
  `S\t:C0\t:C1` where the full-IRI reference is
  `S\turn:km:control:C0\turn:km:control:C1`. This affects both KM arms on
  additions, deletions, RBox and disjunction. An IRI mapping failure must be
  distinguished from a missing logical consequence.
* Both KM arms report consistent at ABox revisions 1 and 3, where the source
  asserts membership in two disjoint classes. Analytic expectations and both
  independent fresh reasoners report inconsistency.
* JFact's session arm differs from its fresh arm at RBox revisions 1 and 3.
  Its disjunction session fails restoration at revisions 2 and 4. A successful
  manager/flush call is not evidence of a correct incremental result.

The audit reports 45/48 arms passing per-arm integrity and analytic checks,
before cross-reasoner mismatches are considered. It does not mark this control
suite correct. No benchmark-release success claim follows from these runs.

KM session receipts report:

| Control | Updates | `el_delta` | `exact_rebuild` | Reused fixpoint updates | Route migrations |
|---|---:|---:|---:|---:|---:|
| additions | 20 | 19 | 1 | 19 | 1 |
| deletions | 20 | 19 | 1 | 19 | 1 |
| RBox | 4 | 0 | 4 | 0 | 0 |
| ABox | 4 | 0 | 4 | 0 | 0 |
| equality | 4 | 0 | 4 | 0 | 4 |
| disjunction | 4 | 0 | 4 | 0 | 0 |

The four expressive control histories therefore exercise exact rebuilding,
even though their responses retain a backend object.

## Audit validation and pending panel

A local lightweight fixture checked equality of gzip-derived and saved full
signature digests, rejection of malformed digests, a complete eight-arm
producer-digest audit, and detection of a deliberately changed JFact digest.
The real controls were then audited on Slurm. No KM implementation was changed.

A frozen copy `audit_incremental_final.py` is queued as Slurm job 51981234 after
panel pilot 51981169 reaches any terminal state. It writes
`panel-controls-audit.{json,md}`. Missing, failed or unfinished arms are explicit;
an output directory or a nonterminal measurement file is not proof that a
process remains live. The queued audit is future work, not completed evidence.
