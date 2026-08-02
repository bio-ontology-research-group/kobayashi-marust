# Rejected active-clause redundancy-trie candidate

Detached candidate `8121fec` maintained an exact ordered trie beside each
active clause layer and replaced both forward and backward literal-posting
scans with subset and superset traversal. Randomized linear-oracle tests, the
shared-base differential, and the complete local release suite passed: 1,946
tests passed, eight were intentionally ignored, and none failed.

## Provenance

- Source commit: `8121fece689a63541fa2b8d9b60addf9cc5c434a`
- Source archive SHA-256:
  `bd9f655e0cf2cd0fcc38f65282f4467348bf08558aa090428ba072796271668b`
- IBEX build job: `49852630`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `a9f139d2ee0246f05fa362de4605a38dcc8221eee34c047f546628e005d99fcf`
- ORE 1194 gate array: `49852860`, both tasks with checkpoint and
  `TASK_COMPLETE`
- Nineteen-ontology high-resource sentinel array: `49853321`
- Instrumentation-only composition: `0e03350`, archive SHA-256
  `4bc296eba3988b53c76aec284814bafb723d1676dca7cb135f88abb7a4fb62ec`,
  build job `49853316`, binary SHA-256
  `191dd751ff63945f9c49ec6908c0f95291dedb209b30f894afb9b00ede9b449a`,
  profile job `49853372`

All artifacts are retained under
`/ibex/scratch/hohndor/km/candidate-8121fec-active-trie-20260802` and
`/ibex/scratch/hohndor/km/profile-0e03350-active-trie-20260802`.

## ORE 1194 gate

| configuration | status | wall s | peak MiB |
|---|---:|---:|---:|
| automatic route | error | 199.1090 | 2,492.39 |
| manual exact CB, 2 threads, 225-second cap | error | 234.1270 | 1,930.28 |
| same manual run with phase instrumentation | error | 234.2266 | 1,931.49 |
| prior posting-based 2-thread baseline | error | 234.5824 | 12,909.99 |

The lower peak is not a useful memory improvement. The trie build failed to
reach the first 200,000-iteration context profile checkpoint before its cap,
whereas the posting-based profile reached 600,000 iterations. It consumed less
memory because it made much less saturation progress.

## Sentinel result

Seventeen ontologies retained exact baseline signatures. The candidate caused
two operational regressions:

| ontology | automatic route | baseline | candidate | baseline wall s | candidate wall s | baseline peak MiB | candidate peak MiB |
|---|---|---|---|---:|---:|---:|---:|
| 15846 | `certified_nominals` | `ok`, exact | timeout | 197.8516 | 240.0453 | 18,944.27 | 1,923.54 |
| 8480 | `nominals` | `ok`, exact | error | 19.9043 | 190.7933 | 5,426.04 | 1,704.32 |

Several surviving CB-involving rows also slowed, including 11311 from 10.56
to 15.73 seconds and 16744 from 94.64 to 107.53 seconds. The candidate is
therefore rejected and was not integrated. Follow-up candidates isolate trie
subset and superset lookup separately; neither may land without restoring both
sentinel completions and preserving exact signatures.
