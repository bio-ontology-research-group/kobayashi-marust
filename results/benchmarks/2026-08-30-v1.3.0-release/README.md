# KM v1.3.0 release evidence

This directory records the fail-closed ORE 2015 release audit for KM v1.3.0.
The tested automatic classifier was built from commit `5c64a02` using source
archive SHA-256
`e002e94d021a6811716da8a0b7c5e4007426bb2fbc12a6794200c364080c2138`.
The resulting `km` binary has SHA-256
`cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d`.

## Corpus result

The automatic `km classify` route was run on all 592 ORE 2015 ontologies with
a 240-second timeout and 20-GiB process-tree memory limit. Every task used 16
CPUs on an Intel Xeon Gold 6248 node. IBEX jobs `51012720` and `51013597`
produced 592 profiles, 592 results, and 592 byte-identical checkpoints. The
second job resumed 25 tasks rejected before execution on a cluster node whose
actual CPU did not match its advertised feature; it reused the same binary and
harness and excluded that node.

The final statuses are:

- 591 correct completions;
- 588 exact retained-gold signature matches;
- two independently adjudicated retained-gold consistency mismatches;
- one ontology without retained gold;
- one established fail-closed parse error, ORE1194.

All result and signature fields are identical to the v1.2.0 certified sweep.
The 27 differences are execution-route traces and are listed separately in
[`release-gate-summary.json`](release-gate-summary.json). This separation is
intentional: route choice is provenance, while status, verdict, consistency,
signature, taxonomy cardinalities, and mismatch counts remain release-blocking
semantic fields.

## Aggregate metrics

Metrics are over the 591 correct completions:

| Metric | Value |
|---|---:|
| Mean wall time | 1.494590 s |
| Median wall time | 0.1376 s |
| Mean peak process-tree RSS | 221.573 MiB |
| Median peak process-tree RSS | 27.19 MiB |

The aggregate audit is
[`release-gate-summary.json`](release-gate-summary.json). Its SHA-256 is
`e894fc4a36e8e7760dd87b748b1eba18ee2b4ec520aea1c84bafb1290c28136e`.

## Certification and interface gates

The exact source commit passed all four release certification gates:

- `lean/run-ht-certification-gate.sh`;
- `lean/run-elc-certification-gate.sh`;
- `lean/run-cb-certification-gate.sh`;
- `lean/run-routing-certification-gate.sh`.

The routing gate includes the incremental-revision and source-axiom explanation
capstones and their Rust differential tests. The public theorem audit found no
`sorryAx`; reported dependencies are limited to `propext`, `Classical.choice`,
and `Quot.sound`.

The OWLAPI suite passed 31 of 31 tests. The packaged plugin also passed
`protege/run-installation-smoke.sh` in a stock Protégé 5.6.6 OSGi installation,
including native classification, a retained non-buffering update, and a
source-axiom explanation in one session.
