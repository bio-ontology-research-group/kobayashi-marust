# Asserted edges through nominal merge chains (2026-10-31)

Agent `bridge-merge-edges`, branch `fix/v155-bridge-merge-edges` off
development/v1.5.5 ba20e5f5. Defect, fix and exactness argument:
docs/HYBRID-CB-HT.md section 10, subsection "Asserted edges through merge
chains".

## Binaries (scratch `.work/agent-scratch/bridge-merge-edges/`, not committed)

- `km.after`: the bridge-nominal-merge `km.after` (sha256 21c97526...834e),
  the baseline the brief names.
- `km.fix1`: `cargo build --release --bin km` of commit 8f076ee7 (the later
  commits on this branch touch only docs and results; 8f076ee7's test-only
  edits in `bridge.rs`/`u15.rs` were made after this build and do not enter
  the binary), sha256 3aa90255...6a06.
- `km.trace2`: `km.fix1` plus env-gated (`KM_MERGE_TRACE=1`) eprintln at
  every stop of `merge_individual_node_into` and every `false` return of
  `install_native_role_assertion_edge`; diagnosis only, the edit was
  reverted, sha256 40913d9e...d879.
- Oracle: HermiT 1.4.3.456; gold caches of r3-unannounced and
  bridge-nominal-merge.

All runs: `KM_THREADS=1`, at most 3 KM processes at once, workstation load
25 to 50 on 56 cores.

## Files

- `five-fix1.tsv`: r1164, r281, r947, r2627, r2970, forced bridge and
  automatic route, 120 s cap: 10/10 ok, each in 0.01 s.
- `extra-r3.tsv`, `extra-g.tsv`: the six seeds that km.after declined after
  answering them wrongly before (r1536, r1866, g545, g789, g1344, g1551):
  12/12 ok.
- `gen-fix1.tsv`: 2,000 `gen_merge.py` seeds, 30 s. km.after: bridge 1,769
  ok / 231 declined, auto 1,956 ok / 44 timeouts. km.fix1: bridge 1,993 ok /
  7 declined, auto 2,000 ok. 0 wrong; no seed answered by km.after is lost.
- `r3-{tpl,tpl2,seeds}-fix1.tsv`: R3 sets (tpl and tpl2 20 s, random seeds
  10 s). tpl and tpl2 identical to km.after (1,929 / 71 declined and 968 /
  32 declined on the bridge, auto 1,999 + 1 timeout and 1,000). Random
  seeds: km.after bridge 3,134 ok / 866 declined, auto 3,558 ok / 442
  timeouts; km.fix1 bridge 3,333 / 667, auto 3,738 / 262. 0 wrong; every
  change is to ok.
- `alc/`: the 2026-10-29 bridge seed sets (`eval.py` of cb-inverse-top,
  60 s), identical per seed to km.after: auto 694 ok / 1 WRONG (621) / 3
  TIMEOUT and 295 / 2 WRONG (1014, 1022) / 3; bridge 654 ok / 43 DECLINE /
  1 TIMEOUT and 279 / 18 / 3. The three wrong answers are the missed
  inconsistencies recorded by bridge-nominal-merge as predating it.
- `err-trace.tsv`: every remaining forced-bridge decline of the four seed
  sets above (777) run on `km.trace2`: none reaches a stop in
  `merge_individual_node_into`; 773 are "ABox conversion was incomplete"
  (repeated assertions and other admission declines), 4 (g155, g1220,
  g1234, g1489) defer elsewhere.
- `ore/times-{after,fix1}.tsv`: the 112 nominal ORE inputs of the paired
  design half (`r3-unannounced/ore-design-nominal.txt`), automatic route,
  300 s, both streams side by side with `KM_THREADS=1`. 108 answered by
  both, all signatures identical, same route on every input; the same three
  time out on both (16420, 1833, 2548) and 8250 exits 3 on both. Sum 728.1 s
  after, 725.8 s fix1; time ratio mean 1.034, median 1.006 (inputs of 1 s
  or more: mean 1.020, median 0.989).
- `tools/`: `chain.sh` (all seed sets for one binary), `ore.sh`, `five.sh`,
  `trace.sh`, `cmp.py` (verdict counts and per-file changes between two
  diff_run tables).

## Tests (release)

- `cargo test --release --lib konclude_ht`: 1,514 passed, 0 failed, 7
  ignored.
- The 17 bridge and nominal integration binaries of bridge-nominal-merge
  plus the new `bridge_merge_chain_edges`, `--test-threads=1`: 18 binaries,
  56 passed, 0 failed, 1 ignored (`nominal_seq_order`, which timed out once
  for bridge-nominal-merge under load 140, passed 6/6 in 19 s).
