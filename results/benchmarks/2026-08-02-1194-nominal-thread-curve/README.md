# ORE 1194 nominal-CB thread and budget curve

This experiment tested whether the final automatic-route failure could be
closed by balancing CB parallelism against the route's 18-GiB internal memory
watchdog. It used the certified shared-base source at `02a563f` and changed
only the selected `nominals` route's worker count and central time budget.

An initial array (`49845412`) attempted to set `KM_THREADS=2/4/8` in the parent
environment. That was not a valid thread-count comparison: automatic routing
normalizes the selected bundle after reading the parent environment, and the
bundle's common 16-thread default replaced all three values. The harness rows
correctly recorded the requested environment, but every worker ran the same
16-thread route. Subsequent candidates set the count inside `NOMINALS` itself.

## Valid production gates

| candidate | commit | build | gate | wall s | peak MiB | terminal cause |
|---|---|---:|---:|---:|---:|---|
| 16 threads, 190 s central cap | `02a563f` | `49841036` | `49841342_33` | 32.0151 | 18,558.06 | internal memory watchdog |
| 4 threads, 190 s central cap | `5f4ed65` | `49845575` | `49845578_33` | 87.0116 | 18,471.01 | internal memory watchdog |
| 2 threads, 190 s central cap | `b28a479` | `49846414` | `49846426_33` | 199.6904 | 12,887.62 | central time cap |
| 2 threads, 225 s central cap | `644e57c` | `49846966` | `49846975_33` | 234.5824 | 12,909.99 | central time cap |

Every row selected the automatic `nominals` route and failed closed without a
taxonomy. Four threads merely delayed memory exhaustion. Two threads fit the
memory contract but did not reach fixpoint even after using 225 seconds of the
240-second end-to-end allowance; frontend and supervisor work consumed about
9.6 seconds, leaving no useful additional central budget.

The focused route-setting test passed for the four-thread candidate. These
changes affect scheduling only, not calculus consequences. None was integrated
into `main`, and no full sweep was warranted because none improved coverage and
the slower bundle would regress every ontology selecting this route.
