# v1.4 compact positive-EL ABox output

This experiment removes the string-expanded taxonomy from the certified
positive-EL ABox path. The ABox consistency check and named-class taxonomy use
the same EL completion fixpoint as before. The orchestrator now consumes its
dictionary-coded rows directly.

Commit `ce04b506660d107a88f2b8a194cfba26f8f058d8` was built on IBEX from source
archive SHA-256 `2e56e60da3ddc5277756927214f49353df4b1af8c07c97de65db0f0a56b4d955`.
Build job `51262850` produced binary SHA-256
`1646d8033b9e79134d72a317db71e5ec9e0464a919e714f936549be9df9e377b` and
passed the deployment checker.

## Validation

The focused Rust regression runs both output representations over the same
identity-bearing positive ABox and checks equal consistency and named-class
taxonomy. The change affects output representation and orchestration only; it
does not change an EL or CB inference rule and requires no calculus
re-certification.

IBEX arrays `51262877` and `51262912` interleaved the retained production
binary and candidate for five repetitions on each ontology. All 20 jobs wrote
their expected result, timing record, normalized-output hash, and explicit
completion marker. Each ontology had one shared normalized-output SHA-256
across both arms and all repetitions.

| ontology | arm | observations | median wall (s) | mean wall (s) | median peak RSS (MiB) | mean peak RSS (MiB) |
|---|---|---:|---:|---:|---:|---:|
| ORE 1579 | control | 5 | 9.30 | 9.250 | 819.59 | 820.01 |
| ORE 1579 | compact | 5 | 8.71 | 8.522 | 819.67 | 819.72 |
| ORE 6722 | control | 5 | 3.56 | 3.550 | 312.98 | 313.09 |
| ORE 6722 | compact | 5 | 3.27 | 3.372 | 313.11 | 313.19 |

The changes are useful but do not close either strict residual. ORE 1579 must
beat 2.4938 seconds and 596.66 MiB; ORE 6722 must beat 1.8636 seconds and
428.45 MiB. The evidence-composite score therefore remains **524/589**, with
correctness coverage unchanged at **592/592**.

## Rejected in-process variant

An earlier candidate also admitted identity-bearing sources into the
in-process frontend and retained the typed clause set. Array `51262573`
produced ten correct, identical outputs on ORE 1579, but median peak RSS rose
from about 840 to 847 MiB. Phase timings showed that a 0.6-second frontend
gain was offset by slower indexing over the parser-owned clause layout. Commit
`ce04b50` restores the isolated frontend boundary while retaining compact
output.

The local evidence archive contains 106 checksum-manifest entries. Its
`SHA256SUMS` file hashes to
`4ac86e1b17eb2e5d2d0b6c5078fc96afd0e6f4b41071bbe2be995563cc0f0342`.
