# Timings (workstation, load 50 to 140 on 56 cores; medians of three runs)

`tools/time.sh <km> 3` on `hub_data.ofn` (seconds; every run printed the
same 6 output lines, md5 16c23aba):

| binary | auto | nominals | certified_nominals | nominal_ni_abox | certified_card_proxy_abox |
|---|---|---|---|---|---|
| km-e62a4bce | 0.54 | 0.63 | 0.54 | 0.62 | 0.61 |
| km-devhead (97515f0c) | 9.25 | 9.98 | 6.54 | 8.32 | 9.49 |
| km-66297f9f (first commit with both lines) | 8.31 | 7.68 | 6.02 | 9.97 | 8.53 |
| km-66297f9f, `KM_CB_KEEP_INERT_SORTS=1` (auto) | 0.54 | | | | |
| km-a2e98d95 | 0.02 | 12.44 | 8.32 | 15.55 | (stopped) |
| km-base-6c48c72e (load ~120) | 0.07 | 32.65 | >60 (3 of 3) | 26.88 | 33.15 |
| km-perf5 (this branch, load ~60) | 0.02 | 0.53 | 0.55 | 0.55 | 0.63 |
| km-perf6 (this branch, final, load ~120) | 0.08 | 1.75 | 1.86 | 2.15 | 2.11 |

CB engine alone on the captured worker inputs (`km engine`, one thread):
`engine-input/released.json` 5.98 / 8.85 s, `sorted.json` 0.30 / 0.31 s,
`released-without-value-identity.json` 0.23 s.

ore_ont_10781, automatic route (output md5 7a75c2e6 everywhere):
v1.5.4 km-pgo-use 1.9 s, nominal-coverage km-basem (e1881695) 2.4 s,
data-values km-base (284b2acf^) 2.5 s, km-v155-rc (3d5d0f6e) 17.0 s,
km-v155-final (0188fcc7) 16.6 s, km-e62a4bce 16.4 s, km-base-6c48c72e
13.2 / 13.2 / 13.2 s (15.9, 16.2 s at load 120), km-perf5 0.63 / 0.61 /
0.60 s, km-perf6 2.9 / 2.1 / 1.4 s (load 120). Bridge alone
(`KM_ROUTE=ht_bridge KM_DATA_ASSERTION_AS_CLASS=1`): km-base 2.4 s,
km-v155-rc 53.5 s, km-a2e98d95 60.1 s; `KM_HT_NATIVE_FULL=1` on
km-a2e98d95, automatic: 0.66 / 0.66 / 0.74 s.

open_r3602, forced `nominals` (HermiT: 7 subsumptions): km-e62a4bce 0.16 s
with 6 (the r1600 defect), km-66297f9f and km-a2e98d95 and km-base-6c48c72e
>60 s, km-base-6c48c72e with `KM_CB_KEEP_INERT_SORTS=1` 4.1 s (10.4, 14.4 s
at load 120), km-perf5 5.4 / 4.4 / 4.2 s, km-perf6 11.6 / 14.0 / 16.9 s at
load 120, all with 7. Automatic and `certified_nominals` answer in 0.02 s
on every binary.

ORE 9800, automatic (md5 a8aaf5d5): km-a2e98d95 12.9 s, km-base-6c48c72e
11.9 / 11.8 s (15.1 s at load 120), km-perf5 10.9 / 10.2 s, km-perf6 12.8 /
12.7 s. Intermediate km-perf2/3 (filler kept on every object at-most):
42 / 40 / 64 / 60 s, the CB arm 2.3 s to 30 s; that variant was dropped.

m2197, forced `certified_nominals`: km-a2e98d95 0.57 s, km-base-6c48c72e
>60 s, with `KM_NO_MERGE_HYPOTHESES=1` 0.23 s (same 3 subsumptions);
`nominals` >40 s, `nominal_ni_abox` 20.1 s, `certified_card_proxy_abox`
>40 s; with the hypotheses off 2.3 / 2.4 / 2.1 s.

Seeds (`gen_nomdata.py --no-inverse` 2000-2399, `diff_run.py`, 3 workers per
binary, both binaries side by side, HermiT gold): automatic 60 s,
km-base-6c48c72e 364 ok / 36 timeout, km-perf6 363 ok / 37 timeout, 0 wrong
in both (m2336 47.9 s against a 60 s timeout); sum over the 363 both answer
106.3 s against 93.6 s. Forced `nominals` 60 s (394 of 400 seeds; the run
was stopped at the supervisor's load request): 245 ok / 149 timeout each,
0 wrong; m2291 gained (59.4 s), m2336 lost (58.0 s base); sum over the 244
both answer 444.3 s against 464.9 s.
