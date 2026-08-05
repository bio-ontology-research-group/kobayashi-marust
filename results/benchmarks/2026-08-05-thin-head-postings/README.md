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

[`automatic-results.tsv`](automatic-results.tsv) contains all 592 result rows
and has SHA-256
`64db7bd1293ca2aa5a06b0f1cbe1f62edd335723a6406fe7909014e13ff826fd`.
The follow-up design tags spill state in the inline words so hot reads do not
dereference the `ThinVec` allocation merely to decide which slice to return.
