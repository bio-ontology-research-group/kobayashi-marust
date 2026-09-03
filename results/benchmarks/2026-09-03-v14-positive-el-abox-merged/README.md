# v1.4 merged positive-EL ABox consistency certificate

This milestone replaces exact per-individual EL materialization with a
one-node over-approximation when that abstraction proves consistency. Mapping
every source individual to one root, unioning all asserted classes, and
turning every asserted role into a self edge is a homomorphism from the real
ABox into the abstract one. Therefore, if the abstract root does not derive
bottom, no real individual derives bottom. If the abstract root does derive
bottom, KM reloads the unchanged input and runs the established exact ABox
completion. The certificate can save work but cannot change an answer.

The compact output decoder also recognizes the EL interner's `⊥` spelling.
Tests cover accepted safe abstraction, a false cross-individual clash that
must decline to exact completion, and a genuine node-local clash. No EL or CB
inference rule changes.

## IBEX validation

Build job `51265277` compiled commit
`97487bb00489ef4fcdd54a3e3273d557f599a355` from source archive SHA-256
`fd6e75a68baa5a4be5f8bb23d8b99ac2e6d0b14821bd36ec198132c71ff8d1e2`.
The deployment checker accepted binary SHA-256
`97fe2254165cf5327ada7b24be98bce664f4125a2e5bb9605aff89e8dd626c9e`.

Array `51265369` interleaved five control and five candidate runs on each of
ORE 1579 and 6722. All 20 jobs produced results, timings, normalized hashes,
and explicit completion markers. Each ontology had one normalized output hash
across every control and candidate run. The merged abstraction accepted all
ten candidate runs; no exact fallback was needed.

| ontology | arm | observations | median wall (s) | mean wall (s) | median peak RSS (MiB) | mean peak RSS (MiB) |
|---|---|---:|---:|---:|---:|---:|
| ORE 1579 | control | 5 | 8.58 | 9.336 | 820.36 | 821.83 |
| ORE 1579 | merged | 5 | 5.68 | 6.488 | 472.41 | 472.09 |
| ORE 6722 | control | 5 | 3.59 | 3.588 | 312.80 | 312.84 |
| ORE 6722 | merged | 5 | 3.42 | 3.290 | 312.88 | 312.94 |

ORE 1579 now beats its 596.66 MiB memory target but remains above its 2.4938
second wall target. ORE 6722 already beat its memory target and remains above
its 1.8636 second wall target. Consequently this milestone does not yet change
the evidence-composite score: **524/589**, with **592/592** correctness.

The archive contains 105 checksum-manifest entries. Its `SHA256SUMS` file
hashes to `6b9c23341236d6e597bff998074204cff46f362354e08ea07ca6f2d486f88791`.
