# Remove the redundant predecessor-arrival vector

Commit `4275690` removes `Context::neighbor_pred`, a write-only `Vec<u32>` that
duplicated every received predecessor-clause id already held by
`neighbor_pred_seen`. Pred reasoning reads the exact body-predicate posting
lists, not the vector. Diagnostics now read the authoritative set length.
Deduplication, posting membership and order, rule scheduling, and the saturation
fixpoint are unchanged.

## Workstation gates

The complete release library suite passed: 1,954 tests passed, eight were
intentionally ignored, and none failed. Two alternating ORE9944 runs emitted
the same output SHA-256
`97a95bbfc29dd4c7228f20740a5c0d886ee196a113b1154d785759ca5d90168f`.
Mean wall improved from 9.395 to 9.135 seconds and mean peak RSS fell from
6,120,162 to 5,973,984 KiB, about 143 MiB. Baseline and candidate both failed
closed with zero output on ORE1194; their one-run peaks were 18,980,824 and
19,003,172 KiB.

## Source-bound IBEX gates

- Candidate commit: `4275690`; its tree is identical to promoted main commit
  `4254fbb`.
- Source archive SHA-256:
  `645b34c9afa256983fd900cdf76c7b08f96002a17758acd76d6f1c198f116fc1`
- Build job: `50057119`, completed in 4:40
- Binary SHA-256:
  `6af50483186155d051c572668312fdfda90613fe92ad251f10fcaa80aa31fa01`
- Ten-ontology panel: `50057137`
- Resumable 592-ontology sweep: `50057302`

The strict audit verified all 592 unique result rows, profiles, checkpoints,
array indices, and full-array terminal receipts; one binary identity; no
temporary files; and ORE4669's collision-sensitive full-IRI fingerprint.
Coverage remained 591/592, with 588 exact matches, two established consistency
disputes, one established no-gold case, and only ORE1194 failing closed. There
were zero status, verdict, signature, or selected-route differences from the
compact thin-posting baseline.

Across the 591 successful classifications, mean peak RSS improved from 808.03
to 806.24 MiB (0.22%) and median peak RSS from 43.19 to 42.52 MiB (1.55%).
The largest reductions were 301 MiB on ORE9944, 181 MiB on ORE7914, 160 MiB on
ORE6682, and 158 MiB on ORE11311. Independently scheduled mean wall was 5.9308
versus 5.8385 seconds (1.58% higher), and median wall was 0.2537 versus 0.2509
seconds. The source-isolated pair was faster, and this change only removes a
write and allocation, so the cross-job wall difference is not attributed to a
new execution cost.

[`automatic-results.tsv`](automatic-results.tsv) contains the 592 rows and has
SHA-256
`bf88c1008073b30f001e169296f9e6e7df8fe35a0ea99568b1e2856e942fe890`.

