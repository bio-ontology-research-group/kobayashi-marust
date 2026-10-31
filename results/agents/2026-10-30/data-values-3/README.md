# data-values-3: three cost regressions on development/v1.5.5 (2026-10-31)

Agent `data-values-3`, branch `fix/v155-data-values-3-perf` off
`development/v1.5.5` (0e1bd99a). Mechanisms, remedies and the exactness
argument: docs/NOMINALS-CB.md, "Two cost regressions of the nominal CB
input (2026-10-31)" and "Conditional-full schedule for data values on the
bridge (2026-10-31)".

## Regressions and culprits

| regression | culprit | mechanism | remedy |
|---|---|---|---|
| `data_value_next_to_universal_role_hub_stays_satisfiable` 0.5 s to 6-15 s per nominal route | 50bf7ba9 (nominal-coverage merge f41b1af4), the inert-sort release | the released excluded middle `→ Q_4 ∨ Q_6` is a live disjunction on data elements that the literal's identity clause equates; `add_clause` 148 ms to 4,646 ms | `inert_sorts::data_guards_sorted`: a disjunctive candidate that guards a data role keeps its sort when generated values are equated |
| ore_ont_10781 automatic 1.1 s to 13-17 s | 1b0f9239 (native data values merge c9602c7f), singleton elision | no singleton clause, so `tin.number` is false and the bridge leaves the conditional-full schedule; prepare phase 0.7 s to 34 s, over the 12 s budget | `bridge::carries_data_values`: a value marker counts as a number feature for the profile |
| open_r3602 forced `nominals` 4 s to no answer in 60 s | 50bf7ba9, the universal-definer elimination (the 4 s answer itself dates from the r1600 merge, which made it complete) | the `⊤` filler of `ClassAssertion(≤1 s, c)` is dropped and the equality fires on every pair of `s`-successors of `c` | `eliminate_universal_definers` keeps the filler of an at-most asserted on an individual (object successors only) |
| m2197 (`top_nominal_data`) forced `certified_nominals` 0.6 s to no answer in 150 s | 8bbbf1f2 (r1600 merge 2f5993c7), the merge hypotheses | `KM_NO_MERGE_HYPOTHESES=1` answers in 0.2 s with the same 3 subsumptions on every nominal route; the hypotheses are the completeness device of section 10 | not fixed here: switching them off changes answers (r1600); reported |

## Files

- `hub_data.ofn`: the test's input (equal to `hub_with_data_values()`).
- `engine-input/sorted.json`, `released.json`: the CB worker's input on the
  hub test with `KM_CB_KEEP_INERT_SORTS=1` and with the release (captured
  with `tools/engwrap.sh` as `KM_ENGINE`); `released-without-value-identity.json`
  is the released set without the identity clause (diagnostic, unsound).
- `timings.md`: the before/after table with every run.
- `seeds-*.tsv`: `nominal-coverage/tools/diff_run.py` on the 400 seeds of
  `gen_nomdata.py --no-inverse` (2000-2399), automatic route (60 s) and
  forced `nominals` (30 s), head binary against this branch.
- `tests.txt`: test counts.
- `tools/time.sh`: median-of-n timing per route; `tools/engwrap.sh`: the
  worker capture.

## Binaries (`.work/agent-scratch/data-values-3/bin/`)

`km-66297f9f` (nominal-coverage branch after its merge of development),
`km-a2e98d95`, `km-base-6c48c72e` (development before the subset-blocking
gap merge, built by the sibling agent), `km-perf` to `km-perf5`
(intermediate builds), `km-perf6` (this branch, final). Also
`.work/agent-scratch/lean-data-values/km-e62a4bce` and
`.work/agent-scratch/data-values-2/bin/km-devhead` (97515f0c).
