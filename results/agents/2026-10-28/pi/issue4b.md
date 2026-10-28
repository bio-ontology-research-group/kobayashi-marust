Follow-up on issue #4. Your fix is reviewed and merged into development/v1.5.4 (as 88c3ff67). Thank you; the patch is correct.

Next: diagnosis only. Do not change code in this step.
Find out why `km classify` on qudt-merged.ttl does not finish in 600 s.

1. Run `KM_TIMING=1 timeout 1800 engine/target/release/km classify --lines <qudt>` and keep stderr in your scratch directory. Report:
   - how long the Turtle conversion and the frontend take;
   - which route is selected;
   - which worker is running when time passes, and whether it finishes within 1800 s.
2. Run `km profile <qudt>` (or the equivalent profile output) and report:
   - the profile summary;
   - the axiom counts by kind;
   - the number of individuals, nominals and data-property assertions;
   - the expressivity.
3. If one route is the obvious bottleneck, try two or three other routes with `KM_ROUTE=<route>` (see `km routes`) and a 600 s budget each. Report time, CONSISTENT, DROPPED and the SUB count for each.
4. Report your findings as a list of facts, with commands and times, marking what you verified and what you inferred.
   Make no commits.
