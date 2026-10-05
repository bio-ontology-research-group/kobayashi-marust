# Unfinished saturation must not publish a taxonomy

The one-second-cap candidate in full audit 53306225 returned taxonomies that
disagreed with Konclude. The preserved 1028 and 11629 outputs still reproduce
those disagreements under the comparison tool. The attached diagnostic receipt
binds the source, binary, output and measurement hashes.

The driver correctly reported unfinished saturation, but its classification
caller extracted per-node verdicts anyway. Ordinary node flags do not establish
global queue completion. A local 1028 trace showed this path answering all 7,335
subjects from an unfinished pass and skipping completion. That local output
happened to agree with Konclude; the cluster failures establish the actual
incorrect-answer regression.

The caller now discards unfinished saturation before extraction, detaches its
ontology references and leaves the subjects for exact completion. Finished
saturation follows the existing path. The regression test is included in the
hypertableau certification gate; all 1,472 hypertableau tests passed, with seven
ignored tests.

Single-CPU local diagnostics of the repaired binary found:

- 15167 completes in 1.28 seconds with the one-second cap and agrees with four
  independent full-DL reasoners.
- 1028 completes in 6.54 seconds with the default budget and agrees with KM's
  retained baseline and Konclude.
- 1028 with the one-second cap does not finish within the 45-second local bound.
  A separate traced 15-second check confirms the unfinished pass is discarded.

These are diagnostic timings, not release performance measurements. The global
one-second cap is removed from the prepared, unsubmitted data-source candidate.
The frozen successor-deadline audit is unchanged. The next performance step is
to interrupt the observed unproductive successor queue cycle selectively while
retaining productive saturation. Full-corpus coverage and speed requirements
remain unproven. Certification and the optimized build of this repair are
tracked separately in `partial-saturation-guard-work-state.json`.
