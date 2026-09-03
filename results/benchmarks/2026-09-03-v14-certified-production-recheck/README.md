# Certified historic production-route recheck

IBEX job `51291957` tested whether two historically fast TBox-only production
routes could safely replace the exact nominal route for ORE 10749 and 15615.
The job ran on an Intel Xeon Gold 6248 node with 16 CPUs, a 20-GiB reasoner
cap, and five interleaved repetitions of each arm. Every run used binary
SHA-256
`420d607931b0d72c8e2c712b19ca33efc53f831c7ac3c14a5e42c034c0f2bf72`,
returned `status=ok`, matched the retained Konclude signature, and emitted a
checkpoint.

| ontology | arm | median wall (s) | target wall (s) | median peak (MiB) | target peak (MiB) | strict result |
|---|---|---:|---:|---:|---:|---|
| 10749 | raw `production_all` | 0.3390 | 0.3748 | 73.10 | 104.69 | pass, but not publishable |
| 10749 | certified `production_all` | 0.5543 | 0.3748 | 108.61 | 104.69 | fail |
| 15615 | raw `production_all` | 0.3404 | 0.3418 | 68.80 | 107.24 | pass, but not publishable |
| 15615 | certified `production_all` | 0.5853 | 0.3418 | 89.76 | 107.24 | fail |

The raw arm omits nominal/ABox semantics and is therefore not an admissible
automatic route, regardless of its matching answer on these two inputs. The
positive-ABox certificate restores the missing semantic condition, but its
measured cost loses the wall-time target on both inputs and the memory target
on 10749. No routing change is integrated, and the evidence-composite score
remains **525/589**.

The accepted local evidence contains 20 results, 20 checkpoints, no temporary
files, the terminal Slurm log with `PANEL_COMPLETE`, and a completed scheduler
record (`ExitCode=0:0`). The combined SHA-256 digest of the sorted per-file
SHA-256 listing is
`ba55e2e68a6daea9693fbc9e0dee0858c6cc44bd28c1042a4613e16d5f2b1058`.

This experiment identifies a narrower optimization target: remove avoidable
serialization, reload, or duplicate-frontend work from the existing exact
positive-ABox certificate. Such an optimization must retain the same accepted
fragment and classification result; bypassing the certificate is not valid.
