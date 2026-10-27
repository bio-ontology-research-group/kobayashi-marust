# Paired routing runs, design half

Same-binary comparison of the v1.5.3 routing policy (`KM_ROUTING_POLICY=v153`)
against the general policy, on the design half of the admitted inputs
(1,123 inputs; `split.json`). Protocol: one core, 240 s, 20 GiB, the v1.5.3
measure and audit modules; see `paired.sbatch` and `run_paired.py`. "Verified"
counts answers that match the gold signature. Times are wall seconds on the
inputs both policies solve. The contract (`docs/V1.5.4-ACCEPTANCE.md`) requires
no wrong answers, no lost inputs, and mean and median ratios at most 1.10.

| Run | Source | Binary sha256 | Slurm array | v153 verified | general verified | wrong | lost | mean ratio | median ratio |
|---|---|---|---|---|---|---|---|---|---|
| 1 | general policy before the role-automaton fix | (superseded) | 54605691 | 1102 | 1094 | 954, 14101 | 8 | 1.160 | 1.072 |
| 2 | after the role-automaton fix, certificate rules withdrawn | dd2dcc41… | 54610950 | 1102 | 1101 | none | 7499 | 0.999 | 1.045 |
| 3 | `2179c50c` (certificate rules restored; universal role; bug 4 and 5 fixes) | d852ddc4… | 54642012 | 1102 | 1102 | none | none | 1.011 | 1.067 |
| 4 | `400f1bdc` (realization; data-range and bottom-property fixes; spelling fix) | 6c02f317… | 54653332 | 1102 | 1102 | none | none | 1.053 | 1.068 |

Runs 3 and 4 meet the contract. Run 1's two wrong answers were the frontend
role-chain encoding, which every clause route shared and v1.5.3 masked by
routing those inputs to the Konclude bridge. Run 2's lost input (7499) needed
the proved source certificates, which the maintainer exempted from the
admission floor.

The extra time under the general policy is concentrated in eleven inputs that
v1.5.3 sent to the Konclude bridge and the general policy sends to
`certified_nominals` (about +195 s in total in runs 3 and 4).

Chunk summaries (`chunks/*.json`) and per-input outputs stay under
`/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/paired-design-<array>/`.
The held-out half runs once, on the frozen candidate.
