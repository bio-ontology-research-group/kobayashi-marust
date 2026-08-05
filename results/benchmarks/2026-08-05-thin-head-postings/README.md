# Compact head-index postings with one-allocation spill

Candidate commit `3eb9805` replaces 24-byte `SmallVec<[u32; 2]>` CB head-index
postings with a 16-byte representation containing two inline clause IDs and a
`ThinVec<u32>` spill. `ThinVec` stores its header and elements in one allocation,
avoiding the two-allocation penalty measured in the rejected boxed-vector
prototype. Posting insertion order, removal order, and slice consumers are
unchanged, so this is a storage-only change with the same saturation fixpoint.

## Workstation gates

The focused test verifies the 16-byte layout, inline-to-spill order, spill-to-
inline compaction, and removal to empty. The complete serial release suite
passed with 1,962 library tests and every binary, integration, CLI, and
documentation test passing.

Two alternating ORE9944 pairs from the rejected boxed prototype established
the opportunity: exact output and a 326–490 MiB peak-RSS reduction. The final
one-allocation candidate retained the result in a fresh pair: exact output
(SHA-256 `97a95bbfc29dd4c7228f20740a5c0d886ee196a113b1154d785759ca5d90168f`),
8.98 versus 9.46 seconds, and 6,040,012 versus 6,517,316 KiB peak RSS.

Two alternating ORE1194 production pairs both failed closed with zero output.
Candidate peak RSS was 18,986,816 and 18,914,100 KiB versus baseline
18,959,520 and 18,984,536 KiB. The pair average improved by about 21 MiB;
failure timing was slower and remains subject to the production watchdog.

## IBEX sentinel

- Experimental source commit: `40a919d`
- Source archive SHA-256:
  `2097da16fd24a98bdffd5639ea56cbd1b82ef0aea9275cc5c224b16d92046af3`
- Build job: `50053422`, completed in 4:50
- Binary SHA-256:
  `8f1e7b064543099e7868adcdb31d5ddd98c55a98225d2ba2132b698947446f1a`
- Ten-task panel: `50053450`

The strict panel audit found ten result rows, profiles, checkpoints, and
terminal markers, one binary identity, no temporary files, nine exact matches,
and the expected fail-closed ORE1194. ORE4669 retained its collision-safe
full-IRI fingerprint. Memory fell on seven successful sentinels and ORE1194.
ORE7246 was an adverse independently scheduled outlier, while ORE3215 was
slower, so promotion is deferred to the complete corpus gate.

## Full 592-ontology gate

The clean minimal source commit is `3eb9805`; its source archive SHA-256 is
`43d491bfe3e5b7ca644d5308170ce3cb23d7bb249409ad91d882e89ea5e773f0`.
Source-bound build `50053783` completed in 4:40 and produced binary SHA-256
`b62bfdaf1eaa40139634e46d8884ae92237ae3cfbf96dd688f20c040d0430aff`.
Resumable array `50054037` completed all 592 tasks.

The strict audit verified 592 unique ontology rows, all indices 0–591, 592
profiles, checkpoints, and terminal logs, one binary identity, no temporary
files or failure markers, and the collision-sensitive ORE4669 full-IRI
fingerprint. Coverage remained 591/592. There were zero status, verdict,
signature, or selected-route differences from the compact-trigger baseline:
588 exact matches, two established consistency mismatches, one established
no-gold case, and the expected ORE1194 error.

Across the 591 paired successes, mean peak RSS improved from 817.18 to 809.02
MiB (1.00%) and median peak improved from 43.14 to 42.70 MiB (1.02%). Median
wall improved from 0.2530 to 0.2503 seconds (1.07%), but mean wall regressed
from 5.7810 to 5.8497 seconds (1.19%). ORE3215 reproduced a material slowdown
in both independent gates: 146.01 to 168.33 seconds in the full sweep and
146.01 to 165.67 seconds in the sentinel comparison. This implementation is
therefore not promoted as-is despite its memory improvement.

[`first-implementation-results.tsv`](first-implementation-results.tsv) preserves
this first complete sweep. Its SHA-256 is
`64db7bd1293ca2aa5a06b0f1cbe1f62edd335723a6406fe7909014e13ff826fd`.

## Tagged-spill implementation and promotion

Commit `ce4835f` tags spill state in the inline words so hot reads do not
dereference the `ThinVec` allocation merely to decide which slice to return.
Its source archive has SHA-256
`2b8c87ee59b617a616770f1f3ccf6ca2d7003426adffb45b5a31fc4f26312be5`.
Source-bound build `50056177` completed in 4:45 and produced binary SHA-256
`a23ff5237e38d58b7d71ab85a03eb6813e5d8dc991f278f04fd72de7fc139490`.
Ten-task panel `50056245` and resumable full array `50056291` used that binary.

The final strict audit verified 592 unique rows, profiles, checkpoints, array
indices, and terminal receipts; one binary identity; no temporary files; the
expected diagnostic captures only; and ORE4669's full-IRI fingerprint. Coverage
remained 591/592, with 588 exact matches, the two established consistency
disputes, the established no-gold case, and only ORE1194 failing closed. There
were zero status, verdict, signature, or selected-route differences against
both the compact-trigger baseline and the first thin-posting implementation.

Across the 591 successes, mean peak RSS improved from 817.18 to 808.03 MiB
(1.12%). Median wall improved from 0.2530 to 0.2509 seconds; the paired median
ratios also favored the candidate for wall and memory. Independently scheduled
mean wall was 5.8385 versus 5.7810 seconds (0.99% higher), while source-isolated
ORE3215 and ORE9944 pairs were wall-neutral. The full gate saved 578.56 MiB on
ORE7914, 571.31 MiB on ORE10621, 559.63 MiB on ORE9944, and 511.99 MiB on
ORE7246. This representation was promoted to `main` as commits `a44c91d` and
`1d7b8dc`.

[`automatic-results.tsv`](automatic-results.tsv) contains the final 592 rows
and has SHA-256
`5ec066e634a630bbe42e3b940b55570aec0c540979a484b752acbc89bcdf5a80`.
