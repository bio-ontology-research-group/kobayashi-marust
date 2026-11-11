# v160-p3-rerun (PARTIAL: suite run in progress)

## Part 1 (committed)
- Class-only request (`try_reference_stage`, engine/src/orchestrate/mod.rs): `meta.named` holds every registered IRI
  (properties too). The request now contains `meta.declared` plus names of `meta.named`/`meta.asserted_classes` that
  are declared, asserted or occur as concept atom in the clause stream. This fixed min_atleast0_gci and
  min_copy_successor_insufficient (a property row `SUB :s :C` / wrong rows); datatype_union_cover and g633 agree too.
- Unsatisfiable classes are published as unsatisfiable only (no `SUB u x` rows), the canonical minimal form.
- Decline reasons of a non-zero checker exit are cut to 200 characters and carry the exit status (the first output line
  of the checker can be the whole matrix: one TSV row had grown to 2.4 GB before this fix).
- Digest normalisation (tools/run_p3_suite.py, `parse_answer_digest`): `U SUB X` is entailed for every X when U is
  unsatisfiable and production routes print a route-dependent subset of those rows, so SUB pairs whose subclass is in
  the UNSAT set are dropped before hashing; a pair with a satisfiable subclass and unsatisfiable superclass cannot occur
  and is reported by prefixing the digest with `ANOMALY-`, not dropped. The test file uses the same normalisation.
- Tests: `--test reference_stage` 12 passed, 0 ignored. Library suite: 3121 passed, 21 failed, the same 21 names as the
  baseline (no newly failing test).

## Part 2 (partial)
`data/p3-results.tsv` holds the rows finished so far (resumable runner; the run continues in the background and
appends rows, see HANDBACK). `python3 -I tools/analyse.py data/p3-results.tsv ../v160-recognizer-perf/p2-recognition.tsv`
prints per-route and per-reason counts, the four checks and the recognised-but-unpublished list.
Status when this file was written (about 990 of 1781 inputs): see HANDBACK for the numbers; 0 digest mismatches, 0 anomalies.
