# Direct compact output for acyclic NF1 closure

The acyclic-NF1 candidate initially converted every integer closure pair into
owned superclass strings. The worker's established compact-output path then
interned those strings back into integer IDs. Dense ORE taxonomies contain
roughly 14–15 million pairs, so that round-trip costs wall time and keeps
repeated strings live near the process peak.

This candidate adds a worker-only result field carrying the original interner
dictionary and integer relation rows. `km elc` writes those rows directly with
the existing versioned compact protocol. The decoder and orchestrator are
unchanged. The public `elcomplete::classify` API, incremental API, partial
certificate path, sparse worker JSON, and every non-NF1 route retain their
existing string-map contract.

The direct writer validates every subject and superclass ID before emitting
bytes. Focused tests cover ordinary NF1 closure, worker-mode coded rows, binary
round-trip identity, invalid-ID rejection, cycle fallback, and bottom fallback.

## Native build and smoke

IBEX build job `50840842` passed four focused tests and produced release binary
SHA-256 `e6299cd9eaf928d07426ec39449ae8c8eaef1bc5ece838c81dc951eec4bb381e`.

Nonexclusive Gold-6248 smoke job `50840991` compared it with the immediately
preceding acyclic-NF1 binary. Both matched the retained ORE10689 signature
`be6be6663ffd9721606bf3cb61308789c55c28ffbe8d4ba2d85d0ee60b7fcc0f`
and reported 14,809,043 subsumptions. The string-round-trip baseline took
27.5621 seconds at 1813.20 MiB; direct compact output took 23.0162 seconds at
1814.89 MiB. Wall fell by 16.49%. The small peak increase is measurement noise
and means this smoke does not establish a memory improvement. The shared-node
run proves activation and semantic identity, not release-level performance.

Phase-profile job `50841146` is queued to separate frontend, completion,
handoff, mapping, and serialization costs without canonical-fingerprint time.
