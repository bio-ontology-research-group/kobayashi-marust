# KPSet special-reference and partial-saturation experiment

This experiment measures the Konclude-style saturation construction changes:

- named subsumer special-reference dependencies;
- copy versus substitute construction modes;
- potentially-existing flags only for existential/cardinality fillers;
- monotonic positive-label retention from a budget-limited saturation pass;
- KPSet candidate-state and pseudo-model pruning before completion probes.

The initial `7914` A/B comparison uses the previous final binary and the new
binary with identical resources, a 120-second saturation budget, and a
420-second process timeout. Full five-ontology measurements follow only after
checking that this short comparison changes classification progress without
changing soundness.

## Results

The IBEX release build was Slurm job `48607697`, SHA-256
`f90f7e5b7a5f053b3a7b9180844427ff4e274f271b6c977dbbb1674401dff6cc`.

Short A/B job `48607711` retained positive saturation labels for 17,643 of
17,680 subjects in the new build, whereas the old build discarded the entire
budget-limited pass. Both variants nevertheless timed out after seven minutes
without completing a classification round.

Full sweep job `48607977` used 8 CPUs and 64 GB per task, a 10-minute
saturation budget, and a 28-minute process timeout. All five tasks timed out,
so no output taxonomy was available for comparison with the stored Konclude
signatures.

| ontology | status | final classification progress |
|---|---|---:|
| 3215 | timeout | no useful progress report |
| 7914 | timeout | 833 / 17,680; 82 deferred |
| 9663 | timeout | 9,537 / 58,184; 72 deferred |
| 9724 | timeout | no useful progress report |
| 14817 | timeout | 47,041 / 58,364; 60 deferred |

The previous build reached 769 subjects on `7914`, but reached exactly the
same final reported positions on `9663` and `14817`. Thus the special-reference
construction and retained partial labels are active, but they do not remove
the dominant completion bottleneck. The measured solved count remains **0/5**.

## Current checkpoint: 2026-07-11

Work is paused with all diagnostic Slurm jobs stopped. None of the remaining
five ontologies (`3215`, `7914`, `9663`, `9724`, and `14817`) has been newly
solved. The current investigation is focused on ontology `7914`, isolated to
subject index `13031` (`UBERON_0009732`, KM named-concept tag `13041`).

### Established side-by-side result

Konclude and KM hand the same relevant result from saturation to completion:

- the root saturation label contains 282 concepts;
- it contains exactly five existential restrictions and their five paired
  `CCAQCHOOCE` concepts;
- the five role/filler pairs agree semantically between the two reasoners;
- KM's deterministic saturation-expansion cache does not add choice `43541`.

The five expected KM choices are `43540`, `34199`, `34185`, `34135`, and
`44640`. Konclude completion creates only the corresponding five successors.
KM formerly appeared to start completion with additional choices, but the
lower-level insertion trace corrected that interpretation: KM starts with the
correct 282-concept label and derives the extra choices only after completion
rule processing begins.

### First proven divergence

The first unwanted KM choice is `43541`, whose positive operand is existential
concept `134066`. Low-level insertion tracing shows this exact derivation:

```text
applyORRule
  -> add positive superclass concept 5229
  -> applyANDRule(5229)
  -> add positive choice 43541
  -> choose 134066
  -> create an unwanted successor
```

Concept `5229` is a positive `CCSUB` with operands including `43541` and the
other concepts responsible for the unwanted successor restrictions. It is not
copied directly from the saturated label into the AND processing queue.
Instead, `applyORRule` adds it as a fresh branch immediately after
`SAT-ROOT-READY`. The first insertion is new (`contained=false`); later OR
attempts to add it find the existing descriptor (`contained=true`).

This rules out the following as the immediate cause of the `7914` root
fan-out:

- saturation common-concept extraction;
- direct saturated-label copying;
- deterministic saturation-cache replay;
- the five expected automate-choice descriptors;
- successor expansion itself.

The active mismatch is now OR planning/absorption before the unwanted AND
unfold. KM branches into `5229` where Konclude does not. The remaining
possibilities to distinguish are an incorrect label-membership/polarity test,
missing planned-branch restriction behavior, different branch selection, or
Konclude's satisfiable-cache disjunction absorption.

### Port and validation state

Konclude's `addConceptToIndividualSkipANDProcessing` passes the member-function
pointer `&applyANDRule`. KM previously passed the same sentinel as "no skip".
The port now has a distinct `TABLEAU_RULE_APPLY_AND` handle and suppresses the
same positive/negative operator dispatches as Konclude. The focused test
`unit04_add_concept_skip_and_processing_does_not_queue_and_rule` passes on
`ws`, and `cargo check --release --tests` passed before the final OR diagnostic
edit. This faithful correction did not by itself solve the isolated subject,
because `5229` is introduced later through `applyORRule` rather than direct
saturation replay.

Temporary gated diagnostics remain in the worktree. The latest diagnostic in
`completion/u09.rs` would print every OR containing a watched operand together
with each operand's effective polarity and current label membership. Its IBEX
build (job `48637309`) and the concurrent workstation check were stopped at the
pause request, so that final edit has not yet been compiled or executed.

### Resume point

1. Compile the broad OR diagnostic once on `ws`, then build it on IBEX through
   Slurm.
2. Run the isolated `7914` subject with watched operand `5229` and capture the
   parent OR tag, all operands, effective polarities, and membership decisions.
3. Instrument the corresponding Konclude `planORProcessing` and
   `executeORBranching` decision for the same semantic OR.
4. Compare the first divergent decision and port that exact Konclude behavior.
5. Add a focused regression test, rerun subject `13031`, then test full `7914`.
6. Move to the next remaining ontology only after `7914` is solved and its
   result is checked against the stored Konclude signature.

Relevant diagnostic jobs were Konclude root trace `48634528`, KM saturation
handoff `48635819`, KM completion search `48636272`, low-level insertion trace
`48636755`, and parent-AND trace `48637021`.
