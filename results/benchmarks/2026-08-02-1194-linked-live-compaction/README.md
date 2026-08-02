# ORE 1194 linked live-only compaction screen

This candidate compacted the insertion-order linked worked-off arrays whenever
dead slots outnumbered live slots. Compaction followed only live links,
preserved their order, rebuilt positions and links, and discarded dead slots.
It did not improve ontology 1194 and is not included in `main`.

## Provenance and checks

- Parent linked representation: `4a34d3cebf005b380dfd6b721ecbdb83fe5366e3`
- Candidate: `90ffd5375a72608a5be89d92e014ffaafcf1315e`
- Source archive SHA-256:
  `f5d6058f5f1cd18e447fd56443adb856035f3b93baa6c58231de46918c4560d0`
- Seven focused optimized base/delta differential tests passed
- IBEX build job: `49863728`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `f773d23dcdf8a8962cf7205ac983cbc3ba17aa2b4eb580e427cf332244aad962`
- Gold 6248 manual screen task: `49864250_1`
- The task produced a checkpoint, manual route trace, JSON result, and
  `TASK_COMPLETE`

## Result and decision

The exact two-thread manual CB route failed closed after 233.8162 seconds at
14,896.48 MB. The uncompact linked parent failed after 233.7743 seconds at
14,904.05 MB in its comparable screen. Live-only compaction therefore changes
neither wall time nor peak memory materially.

Reject the candidate. No automatic or sentinel gate was needed after the hard
manual screen showed no benefit. Further work targets the measured active and
head posting deletion cost instead of linked-slot storage.

