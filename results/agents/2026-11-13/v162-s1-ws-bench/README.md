# v1.6.2-rc1 speed on ws: interleaved against v1.5.3 and v1.6.1

Why: the Ibex S1 median ratio was 1.142, 1.306 and (node-paired) 1.183,
while chunks run by the same pair on one node ranged from 0.97 to 1.42.
This run separates the binaries from the node.

How (`bench.sh`): 40 held-out inputs drawn with seed 7 from the 130 that
both binaries verify in the node-paired Ibex runs with a v1.5.3 time of
0.12 to 0.4 s (the median range); for each of 5 rounds and each input,
v1.5.3 (2470b041), v1.6.2-rc1 PGO (67a88998) and v1.6.1 (ed3d8027) in
turn, one km at a time, the S1 flags and `KM_THREADS=1`, output to stdout
as in the protocol. All 600 runs exit 0. Rows: `times.txt`
(round, binary A/B/C, input, exit, seconds).

| comparison | ratio of medians | median per-input ratio | median delta |
|---|---:|---:|---:|
| v1.6.2 / v1.5.3 | 0.951 | 1.002 | 0.4 ms |
| v1.6.1 / v1.5.3 | 0.929 | 1.028 | 2.8 ms |
| v1.6.2 / v1.6.1 | 1.024 | 0.993 | -1.7 ms |

Median times: v1.5.3 0.193 s, v1.6.1 0.179 s, v1.6.2 0.183 s. v1.6.2 is
as fast as v1.5.3 and v1.6.1 on median-sized inputs; the Ibex median
ratio comes from the nodes.
