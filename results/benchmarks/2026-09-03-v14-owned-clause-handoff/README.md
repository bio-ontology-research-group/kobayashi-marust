# Move-only normalized-clause handoff

Commit `cebec3e69d4f07970152303ee67dfcc217aa2c2c` converts an owned normalized
frontend clause into worker JSON by moving strings and nested terms instead of
cloning them. The wire representation and derived clause set are unchanged.
The focused differential test covers every term shape, and the complete
frontend test selection passed 169 tests with no failures.

IBEX build job `51276807` produced candidate binary SHA-256
`420d607931b0d72c8e2c712b19ca33efc53f831c7ac3c14a5e42c034c0f2bf72`
from source archive SHA-256
`94150b154542e7c00f8191702a737240e06407852fe42a4107d89c5b75dac6b7`.
Paired job `51277348` ran the parent and candidate on all eight exact-EL
performance residuals, interleaved with three repetitions per arm. It produced
48 result files and 48 checkpoints, ended with `PANEL_COMPLETE`, and every run
used route `elc`, returned `status=ok`, and matched the retained gold
signature.

| ontology | parent median wall (s) | candidate median wall (s) | wall ratio | parent median peak (MiB) | candidate median peak (MiB) |
|---|---:|---:|---:|---:|---:|
| 6722 | 3.6772 | 3.6888 | 1.0032 | 314.19 | 313.89 |
| 7340 | 3.2559 | 3.1590 | 0.9702 | 291.90 | 292.43 |
| 7868 | 4.3097 | 4.1697 | 0.9675 | 302.04 | 302.17 |
| 12087 | 4.3067 | 4.2876 | 0.9956 | 358.64 | 359.78 |
| 12387 | 4.5125 | 4.4959 | 0.9963 | 405.65 | 405.34 |
| 13224 | 4.5308 | 4.4276 | 0.9772 | 396.80 | 396.71 |
| 15976 | 5.3131 | 5.2345 | 0.9852 | 352.71 | 352.64 |
| 16596 | 5.0644 | 4.9282 | 0.9731 | 361.12 | 362.47 |

The seven active cases improve by 0.4--3.3% in median wall time. ORE 6722
declines the exact-EL in-process screen and therefore does not use this
handoff. Peak RSS changes remain within 0.4%, and no ontology crosses both of
its external time and memory targets. The evidence-composite score remains
525/589.

The retained local evidence manifest has SHA-256
`ced0ec52635d49bf6ad98d0b67010eec6a25cd7bff94d5a23193bd82dc3f3cde`.
The pre-change phase profile is retained separately under
`.work/artifacts/v14-elc-residual-phase-profile/`; it shows frontend work as
the largest phase on six of the eight inputs and EL saturation as the largest
worker phase on ORE 13224 and 7868.
