# Certificate defects of the checkers-on suite (agent `certificate-defects`)

2026-10-30/31, branch `fix/v155-certificate-defects` off `development/v1.5.5`
(97515f0c), with `development/v1.5.5` merged at 5c268416 and 0e1bd99a.
Sub-branches merged in: `fix/v155-certificate-defects-cb` (C1, C2, C3, B1,
B2 layer 1) and `fix/v155-certificate-defects-ht` (H1, T1). Design notes,
exactness arguments and Lean obligations: `docs/CHECKERS-ON.md` section 5,
`docs/CB-CERTIFICATION.md` ("Checkers-on certificate defects C1-C3, B1, B2
(2026-10-30)"), `docs/HYBRID-CB-HT.md` section 10.

## Probes

`probes/*.ofn`: the minimal inputs of the checkers-on suite
(`elc-skolem-pair`, `elc-disjointness-bottom`, `cb-functional-source-encoding`,
`cb-production-standalone-trace`, `cb-production-justification-decode`), the
component inputs (`a-sub-b`, `d-some-r-a`) and `dead-filler` (`D ⊑ ∃r.A`,
`A ⊑ ⊥`, new). With the rebuilt checkers every minimal input is accepted in
modes `on` and `ht` (exit 0; `elc-disjointness-bottom` on
`--route production_all`, the two CB ones also on `--route cb_plain1`).
`d-some-r-a` under `KM_LEAN_CHECKERS_SET=all` still has the six Hyper-based
closure rejections (B2 layer 2, a missing proof, see below).

## Lean

`lake build` of the default targets after all merges: see `lean-build.txt`
(job count, no `declaration uses 'sorry'`). Executables used by the suite:
the 66 listed in `binaries.sha256` of the suite (built from this branch with
`lake build <exe>` one at a time).

## Tests and gates

`tests-summary.txt` (targeted release tests with the real checkers and the
whole lib suite without checker env) and `gates-summary.txt` (the five
gates). Scripts: `run-tests.sh`, `run-gates.sh`, `routing-rest.sh`.

## Checkers-on suite

`tools/checkers-on-suite.sh KM lean/.lake/build/bin OUT inputs/fixtures.tsv
inputs/seeds.tsv inputs/ore.tsv` with the inputs of
`results/agents/2026-10-30/checkers-on-suite/inputs/`, four runs at a time,
`KM_THREADS=1`, 60 s, `SUITE_GOLD` = the four HermiT answer directories of
that README. `km`: `km-final` (sha256 in `suite/binaries.sha256`), built from
8a417f98. The run was interrupted at 4,114 of 5,343 runs by a host restart
and resumed with the same binaries (finished pairs kept). Results:
`suite/summary.md`, `suite/per-input.tsv`, `suite/results.jsonl.gz`.

| mode | accepted | rejected | cannot_check | over_budget | no_answer | answers changed | wall ratio vs off |
|---|---:|---:|---:|---:|---:|---:|---|
| `on`, before (v1.5.4 checkers, 59306389) | 34 | 231 | 1,014 | 380 | 122 | 0 | 1.16 (1,045 inputs) |
| `on`, after | 535 | 0 | 1,135 | 21 | 90 | 0 | 1.63 (1,669 inputs) |
| `ht`, before | 34 | 365 | 662 | 595 | 125 | 0 | 1.81 (696 inputs) |
| `ht`, after | 596 | 0 | 916 | 178 | 91 | 0 | 2.22 (1,511 inputs) |

No rejection remains, so there is nothing to minimise. Every cached HermiT
answer agrees with every published answer (off 519 ok, on 519 ok, ht 508
ok, no WRONG). The wall ratio is over many more inputs than before (the
answered sets differ), and most of the added time is ELC certificate
production and checking.

`on` accepted: 533 ELC publication certificates and 5 CB taxonomy pairs
(521 ORE, 9 fixtures, 4 cardinality, 1 bridge). `cannot_check` in `on`
is dominated by unchecked HT answers (1,149 events; HT checkers are opt-in),
CB nominal mode (188), the ELC fact budget (76) and ELC residuals that fail
the canonical model check (20). The 21 `over_budget` runs in `on` are 19
ELC inputs whose certificate production or check did not fit in 60 s under
the suite's load, plus ore_ont_11745 and ore_ont_6682 (`production_all`,
`certified_nominals`). Example: ore_ont_12221 (4.8 MB, 760,000 facts,
120 MB certificate): producer 148 s at 8a417f98, 72 s after the borrowed
incoming lists, see `cost.txt` for the last measurement; checker 50 s.
