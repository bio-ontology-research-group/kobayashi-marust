# Missed inconsistencies of ALCHIQ seeds 621, 1014, 1022 (2026-10-31)

Agent `alchiq-regression`, branch `fix/v155-alchiq-regression` off
development/v1.5.5 at ba20e5f5. Defect, fix and exactness argument:
docs/PER-CONTEXT-ORDERING.md section 12.

## Binaries (scratch `.work/agent-scratch/alchiq-regression/`, not committed)

All `cargo build --release --bin km`.

| file | source | sha256 | seeds 621 / 1014 / 1022 |
|---|---|---|---|
| `nominal-seeds/km.final` | 38173913 | f4e3bffc...72a1 | inconsistent (ok) |
| `km.8bbbf1f2` | 8bbbf1f2 (r1600 engine change on the nominal-seeds base) | b5edc710...44bc | inconsistent (ok) |
| `km.b88c6253` | b88c6253 (data-values-2: stop at a global refutation) | 123bc4cc...b9ba | consistent (WRONG) |
| `bridge-nominal-merge/km.after` | 0e1bd99a + bridge-nominal-merge | 21c97526...834e | consistent (WRONG) |
| `km.fix` | d6f9a2db (this branch) | 11fe0a65...314e | inconsistent (ok) |

Switches on `km.after` (`KM_NO_MERGE_HYPOTHESES`, `KM_CONTEXT_PAIR_R2`,
`KM_NO_BRIDGE_OBJECT_GUARD`, `KM_HT_INCRBLOCK2_CHECK`): all three stay
wrong. The CB engine answers (HT-first phase without an answer); `km engine`
on the `km ofn` output reports `"inconsistent":false` at 1 and 4 threads,
and `KM_DUMP_WO` shows one context (the first query) only: the run stopped
before the ⊤ context was created.

Oracle: HermiT 1.4.3.456 (`.work/agent-assets/2026-10-28-scratch/oracle`).
All runs `KM_THREADS=1`, at most 3 in parallel, workstation load 30 to 45.

## Files

- `min/min{621,1014,1022}.ofn`: the seeds reduced axiom by axiom
  (`tools/ddmin.py BAD SRC OUT GOOD`: keep a removal while `km.after` says
  consistent and `km.final` inconsistent); HermiT: all inconsistent. Also
  the test fixtures `engine/tests/fixtures/global_refutation_closure/`.
- `alc/`: the 2026-10-29 bridge seed sets (700 ALCHIQ, fresh 300 from
  `gen_alc.py` 1000 to 1299), `eval.py` of cb-inverse-top, 60 s, automatic
  route and `ht_bridge`. `counts-fix.txt`:
  auto 695 ok / 0 WRONG / 3 TIMEOUT / 2 hermit-error and 297 / 0 / 3;
  bridge 654 ok / 43 DECLINE / 1 TIMEOUT and 279 / 18 / 3. Compared with
  `bridge-nominal-merge/alc/counts-after.txt`: the three WRONG become ok,
  everything else identical (same timeout seeds 285, 471, 490, 1101, 1230,
  1249).
- `out/gen-fix.tsv`: the 2,000 `gen_merge.py` seeds of bridge-nominal-merge,
  30 s, `diff_run.py` of r3-unannounced: auto 1,956 ok / 0 WRONG / 44
  TIMEOUT; ht_bridge 1,769 ok / 0 WRONG / 231 ERR (declined). Identical to
  `gen-after.tsv`.
- `out/r3-{tpl,tpl2,seeds}-fix.tsv`: R3 motif sets (20 s) and 4,000 random
  seeds (10 s), both routes. tpl auto 1,999 ok / 1 TIMEOUT, bridge 1,929 /
  71 ERR; tpl2 auto 1,000 ok, bridge 968 / 32 ERR (identical to after);
  random seeds auto 3,574 ok / 0 WRONG / 426 TIMEOUT (after: 3,558 / 0 /
  442; 16 timeouts became ok, none the other way, consistent with the lower
  parallelism of this run), bridge 3,134 / 866 ERR (identical).
- `timings.txt`: the three seeds, wall time per binary (0.07 to 0.14 s on
  all binaries). ore_ont_7610 (the case the stop was added for), default
  threads, both in parallel: 7.5 s on `km.after`, 7.7 s on `km.fix`, both
  inconsistent.
- `lib-failed-fix.txt`: `cargo test --release --lib -- --test-threads=3`
  without the Lean checker environment: 3,050 passed, 21 failed, 10
  ignored; the 21 names are exactly the list in
  `checkers-on-suite/tests/lib-all-without-checkers.log` (tests that need
  the real Lean checkers).
- `tools/chain.sh BIN TAG`: the whole differential chain.

## Tests (release)

`global_refutation_closure` 2 passed (fails on `km.after`: all six fixtures
answer consistent at 1 and 4 threads); `ht_subset_blocking` 4;
`ht_subset_model_certificate` 3; `merge_hypotheses` 4 passed, 1 ignored (the
existing `#[ignore]`); `nominal_seq_order` 6; `r3_disjunctive_equality` 4;
0 failed.
