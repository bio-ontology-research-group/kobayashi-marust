# Consume fixed hypertableau output pairs

Commit `4942f1e` deserializes each hypertableau taxonomy relation as a fixed
`[String; 2]` and moves both strings directly into the grouped output map. The
previous `Vec<Vec<String>>` representation accepted variable-length rows and
cloned both strings from every valid relation. The fixed representation rejects
malformed rows at the worker boundary and eliminates those clones.

This is an output handoff change only. Hypertableau rules, search, routing, and
the emitted taxonomy are unchanged, so Lean re-certification is not required.
The complete release suite passed with 1,952 library tests, eight ignored, and
all binary, integration, and documentation tests passing. A focused regression
checks malformed-row rejection and exact pair transfer.

The exact source archive has SHA-256
`c8c20d4a1da1799b4698d79fc259c4897f3be42ecffa94745f097921994ed50d`.
IBEX build job `50045041` produced candidate binary SHA-256
`1a479a450f0bcf234375f756f273bc692a480324360f337e203571b45503aff6`.

## Alternating ORE3215 pair

Job `50045042` ran three alternating repetitions against the exact source-bound
`9ee269e` baseline on one exclusive Intel Xeon Gold 6248 node. ORE3215 exercises
the large hypertableau taxonomy handoff. Every complete output had SHA-256
`8f826fab860de64749889786f35a3cf258bc33ed78143faa3e606c903b2d7203`.

| Arm | Wall seconds | Peak KiB |
|---|---:|---:|
| baseline 1 | 151.30 | 5,501,280 |
| candidate 1 | 147.27 | 5,509,572 |
| baseline 2 | 149.80 | 5,511,884 |
| candidate 2 | 148.61 | 5,508,560 |
| baseline 3 | 149.38 | 5,504,500 |
| candidate 3 | 148.12 | 5,507,172 |
| **baseline mean** | **150.160** | **5,505,888** |
| **candidate mean** | **148.000** | **5,508,435** |

Mean wall improved by 2.16 seconds, or 1.44%. Mean peak RSS changed by
+2,547 KiB (+0.05%), which is measurement-neutral. The strict audit verified
all timing and digest receipts, six zero exits, exact source-bound binaries,
and all six output hashes. The scripts in this directory reproduce the build
and pair.
