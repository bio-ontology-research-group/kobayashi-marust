# Checkers-on suite summary

Inputs: 21. Off-mode answers against cached HermiT gold: {}.

## Mode `on`

| outcome | runs |
|---|---:|
| accepted | 9 |
| rejected | 0 |
| cannot_check | 2 |
| over_budget | 10 |
| no_answer | 0 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 11 inputs both modes answer: off 94.3 s, on 437.9 s (ratio 4.64).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| ore | 9 | 0 | 2 | 10 | 0 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| certified_nominals | 0 | 0 | 1 | 0 | 0 |
| elc | 9 | 0 | 0 | 10 | 0 |
| production_all | 0 | 0 | 1 | 0 | 0 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| elc-cert-check | 9 | 0 | 0 |
| ht:none | 0 | 0 | 2 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|
| ht | HT checkers not enabled (set KM_LEAN_CHECKERS_HT=N); the HT answer is unchecked | 2 |

## Mode `ht`

| outcome | runs |
|---|---:|
| accepted | 8 |
| rejected | 0 |
| cannot_check | 0 |
| over_budget | 13 |
| no_answer | 0 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 8 inputs both modes answer: off 26.9 s, ht 310.0 s (ratio 11.51).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| ore | 8 | 0 | 0 | 13 | 0 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| certified_nominals | 0 | 0 | 0 | 1 | 0 |
| elc | 8 | 0 | 0 | 11 | 0 |
| production_all | 0 | 0 | 0 | 1 | 0 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| elc-cert-check | 8 | 0 | 0 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|

