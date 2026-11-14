# KM 1.6.4 release notes

Released 2026-11-14 (tag `v1.6.4`).

## What changes

KM 1.6.4 fixes issue #5. A FLOPO ontology (PO, PATO and 2,139
annotation classes) with 173 negated quality definitions did not classify
in 300 s with v1.6.2 or v1.6.3; the same ontology without the negations
took about 1 s. v1.6.4 classifies it in about 17 s on one thread. No
theorem changes; the Lean development is that of v1.6.3.

- **`km classify` runs with the release flags.** Every release benchmark
  ran km with five flags set (`KM_HT_DDB`, `KM_HT_NATIVE_FULL`,
  `KM_CACHE_CONFORMANCE`, `KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE`,
  `KM_FAST_IRI_GRAMMAR`), and `km incremental` set them itself, but plain
  `km classify` (the command the Protégé plugin runs) did not. Without
  `KM_HT_DDB` (dependency-directed backjumping) the hypertableau bridge
  backtracks chronologically, and on the issue #5 inputs it did not
  finish. `km classify` now sets each of the five flags that the caller
  leaves unset; `KM_NO_RELEASE_DEFAULTS=1` turns this off. Benchmarks and
  `km incremental` behave as before.
- **Fewer and smaller refutation probes in the bridge.** The 173 negated
  definitions cannot be triggered from their parts, so every subject keeps
  them as possible subsumers, and the bridge probed all of them together
  for each of the 1,374 annotation-class subjects (about 880 nodes per
  probe, 119 s in all). Two changes, neither of which changes a verdict:
  - The subject's own model now also rules out a definition when the
    subject was read off without any branching. A definition always
    carries its marker, so a complete, branch-free model of the subject
    that lacks the marker shows that the subject is not under the
    definition. Before, KM used this test only for branching read-offs.
  - The batch probe runs in chunks of at most 16 candidates
    (`KM_BRIDGE_BATCH_CHUNK`, 0 restores one probe). A satisfiable chunk
    rules out exactly its members, as the whole batch did; any other
    result leaves its members to their single probes, as before.
- **Tests and release tools.** The `frontend_check` integration tests
  expect the v1.6.3 SHI route, and the Java release step finds the
  Protégé 5 jar under its v1.6.3 name.

## Issue #5 timings

Workstation, one thread, release build, 300 s limit:

| input | v1.6.3 | release flags only | v1.6.4 |
|---|---:|---:|---:|
| reproducer (base, 136 form (a), 37 form (b)) | timeout | 132 s | 17 s |
| base, 136 form (a), 1 form (b) | timeout | 17.7 s | 8.2 s |
| base, 1 form (a), 37 form (b) | 66 s | 5.9 s | 4.4 s |
| base, 136 form (a) | 13 s | 13.6 s | 8.3 s |
| base, 37 form (b) | 4.5 s | 4.9 s | 4.0 s |
| base | 1.2 s | 0.76 s | 0.77 s |

Form (a) is `S and some has_part (P and not (some has_characteristic D))`,
form (b) is `S and not (some has_part (P and some has_characteristic D))`.

Answers: on base, form (a) only, form (b) only, and a 10 + 5 subset, the
sorted answer is identical to v1.6.2. On the inputs v1.6.2 does not
finish, the answer is identical at every chunk size and thread count, and
it contains both subsumptions named in the issue. A sample of 40 ORE
inputs gives identical answers before and after the bridge change; one
became faster (2.4 s to 1.8 s), none slower.

## Checks for this release

PENDING: Ibex certification from the tag (PGO build, five Lean gates,
Rust suite, Java and checkers) and the S1/C1 speed and correctness runs.

## Known issues

- km rejects literals whose datatype is outside the OWL 2 datatype map,
  such as `xsd:date`, also in annotations, as the OWL 2 DL specification
  requires. The user's full FLOPO workload uses `xsd:date` annotations;
  with them written as `xsd:dateTime` or plain strings it classifies in
  about 20 s.
- The bridge runs one subject worker on the `production_all` route, so
  more threads do not speed up the issue #5 inputs.
- macOS and Windows: as in v1.6.3, the plugin was tested inside Protégé on
  Linux only, and the macOS binaries are not signed.

## Assets

`kobayashi-marust-protege5-1.6.4.jar`, `kobayashi-marust-protege6-1.6.4.jar`
(attached by CI), and the km executables built by CI for the five
platforms (release profile, not PGO).
