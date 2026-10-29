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
| 5 | `b574d11e` (bug 1: at-most-one clauses as fresh nominals, object/data sorts) | d59a672d… | 54669336 | 1099 | 1101 | v153: 14321, 13132, 6951 | general: 9800 | 1.042 | 1.102 |
| 6 | `8a307740` (sorts closed under the clause set; complement excluded middle; data-assertion carry; cause A reverted) | 1390e3e7… | 54693367 | 1094 | 1096 | none | none | 1.056 | 1.048 |
| 7 | `7bfc82be` (profile abstraction for data assertions above the cap; sorts never widen fixed sorts) | 219694e6… | 54707431 | 1087 | 1092 | none | none | 1.053 | 1.060 |
| 8 | `9cf7c2cd` (individuals pinned through their nominal proxies; HasKey as DL-safe rules; non-neutral drops published; Sequoia ordering never auto-selected in nominal mode) | c3fb8abb… | 54741000 | 1094 | 1099 | none | none | 1.009 | 1.098 |
| 9 | `0a0d73c8` (forced routes fail closed; definer sharing; bridge clause path and `≤0`; EMELIM fold; context and base-context ordering regimes; CB r-Succ pool; sort encoding on data properties; bridge data-property gate; subset blocking; rule checker) | a42e3816… | 54786965 | 1094 | 1099 | none | none | 1.081 | 1.088 |

Runs 3 and 4 meet the contract. Run 5 does not: the bug 1 encoding made the
`nominals` route unsound on three inputs that the v1.5.3 policy sends there
after the bridge declines on unsupported data-property assertions (14321:
three satisfiable classes reported unsatisfiable; 13132 and 6951: reported
inconsistent), while `certified_nominals` under the general policy stayed
correct on the same binary; the general policy also lost 9800 (certified
nominal CB 71 s in run 4, timeout in run 5) and its median ratio rose to
1.102. The three wrong answers and the lost input are under investigation
before any further run.

Run 6 meets the paired contract (gained 2792 and 16666), but both policies
verify eight fewer inputs than in run 4: 10425, 1555, 15655, 1672, 1685,
4410, 4572 and 5368 now publish their correct taxonomies with DROPPED in
the thousands, because their data-property assertions exceed the
512-literal cap of the exact assertion carry. v1.5.3 published the same
taxonomies with DROPPED 0 without justification. The contract's
no-coverage-loss condition against v1.5.3 is therefore not met yet; an
exact literal abstraction is in progress.

Run 7: the profile abstraction recovered 1555 and 1672 on the general policy
(and 3010 newly), and the maintainer's amendment of 2026-10-28 covers
10425, 15655, 4410, 4572 and 5368. Seven inputs that run 6 verified through
the ground-rule data source (10702, 14334, 14551, 2826, 5834, 850, 9429) now
time out on both policies: the source's HT structural gate declines after
the sorts fix, and the one-core bridge attempt then exceeds its budget. Under
investigation. Run 1's two wrong answers were the frontend
role-chain encoding, which every clause route shared and v1.5.3 masked by
routing those inputs to the Konclude bridge. Run 2's lost input (7499) needed
the proved source certificates, which the maintainer exempted from the
admission floor.

Run 8 (submitted 2026-10-28 21:08, analysed 2026-10-29 07:20) meets the
contract: no wrong answer, no lost input, mean ratio 1.009 and median ratio
1.098 on the 1,094 inputs both policies solve. The seven inputs run 7 lost
through the declining ground-rule source (10702, 14334, 14551, 2826, 5834,
850, 9429) are verified again under both policies. The general policy gains
2792, 9800, 1555, 16666 and 1672 over v1.5.3 routing on the same binary;
9800 is answered again by the exact nominal regime within the budget. The
largest remaining time difference is the eleven inputs that v1.5.3 sent to
the Konclude bridge and the general policy sends to `certified_nominals`
(+164 s in total, from +200 s in run 7). Run 8 is the candidate for the
freeze unless the open soundness fixes (forced routes fail closed, bridge
clause path) change a published answer, in which case run 9 repeats it.

Run 9 (submitted 2026-10-29 17:19, analysed 2026-10-29 20:00) repeats run 8
from the merged head `0a0d73c8`, which carries every soundness and
completeness fix of 2026-10-29. It meets the contract: 0 incomplete chunks,
no wrong answer, no lost input, 1,094 verified under v1.5.3 routing and
1,099 under the general policy, mean ratio 1.081 and median ratio 1.088 on
the 1,094 inputs both policies solve. The general policy gains 1672, 16666,
1555, 6934 and 2792. Against run 8 the mean ratio rises from 1.009 to 1.081:
the eleven inputs that v1.5.3 sent to the Konclude bridge and the general
policy sends to `certified_nominals` now cost +231 s in total (from +164 s),
and the fourteen `nominals` to `certified_nominals` inputs +124 s; both
groups are answered under both policies. Run 9 is the freeze: the tag is
cut from this head plus documentation commits (the `engine/` tree is
unchanged), the held-out half runs once on the PGO binary built from the
tag, and the G8 comparison uses the v1.5.3 PGO run.

The extra time under the general policy is concentrated in eleven inputs that
v1.5.3 sent to the Konclude bridge and the general policy sends to
`certified_nominals` (about +195 s in total in runs 3 and 4).

Chunk summaries (`chunks/*.json`) and per-input outputs stay under
`/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/paired-design-<array>/`.
The held-out half runs once, on the frozen candidate.
