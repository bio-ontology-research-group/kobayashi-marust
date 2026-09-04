# Deferred engine thread budget in the production race

Workstation evidence for starting the CB stack of `race_cb_vs_ht` before the
supervisor prepares the completion-bridge worker's input. All runs use the
`leechuck-office` workstation, the automatic route, a 16 GiB scope ceiling,
and the retained Konclude gold signatures. This is diagnostic evidence; the
strict IBEX panel and the 592-input sweep remain the release gate.

## Who answers the production-CB residuals

The 23 production-CB residuals of the v1.4 post-partition panel are answered
by the completion bridge or by the EL certificate racer, never by the context
engine, which runs at one thread as the fallback and is killed:

| Case | Production wall (IBEX panel) | Answering worker | Evidence |
|---|---:|---|---|
| 3215, 9663, 11460, 14817, 9724, 16444, 7127, 7956 | 5.9 to 88.3 s | completion bridge | `ht_bridge` matrix wall equals the production wall; CB arms are 5 to 6 times slower or time out |
| 10032 | 5.0 s | EL certificate racer, 0.9 s after starting | process-tree sampling of the production route |
| 4604 | 10.2 s | EL certificate racer, 4.2 s after starting | process-tree sampling; the one-thread CB arm exceeded 16 GiB |

Production timeline on ORE 10032 before the change (wall 4.9 s): frontend
child 1.2 s, then 1.1 s of parent-only work (clause JSON parse, `cb_to_ht`
conversion, tableau input serialisation) before any racer starts, then the EL
certificate racer 0.9 s, then output 0.3 s. On ORE 4604 the parent-only phase
is about 2 s of 10.5 s.

## Alternating pairs

`ab-results.tsv` holds three alternating parent/candidate pairs per input on
the production route. Every candidate JSON output is byte-identical to the
parent output of the same pair, and every output hashes to the retained gold
signature (`df5204236b94...` for 10032, `d07c82fff63f...` for 4604).

| Input | Parent wall (s) | Candidate wall (s) | Parent tree peak (MiB) | Candidate tree peak (MiB) |
|---|---|---|---|---|
| ore_ont_10032 | 5.12 / 5.15 / 5.23 | 4.24 / 4.27 / 4.16 | 394 / 391 / 393 | 354 / 343 / 394 |
| ore_ont_4604 | 10.58 / 11.09 / 11.10 | 8.90 / 9.21 / 8.67 | 2349 / 1698 / 1698 | 1666 / 887 / 1718 |

Tree peaks are 50 ms samples of the summed resident set of every `km`
process, so they are noisier than the harness measurement; they show no rise.
The candidate's `KM_TIMING` trace records the HT worker spawning 1.0 s
(10032) and 2.3 s (4604) after the CB stack started.

## Reproduction

`ab.sh <label> <binary> <ont.owl> <out.json> <err>` runs one bounded
classification and prints wall and sampled tree peak. Inputs came from
`ibex:/ibex/scratch/hohndor/km/corpus/`, gold signatures from
`ibex:/ibex/scratch/hohndor/km/cmp2/out/konclude/`. The IBEX confirmation
should repeat the production route three times per arm on the 23 residuals,
then run the 592-input automatic sweep, as in
`results/benchmarks/2026-09-04-v14-post-partition-cb25/`.
