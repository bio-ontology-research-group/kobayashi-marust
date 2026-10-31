# forced-nominal-data-misses: two data probes missed on the nominal routes

Agent `forced-nominal-data-misses`, branch `fix/v155-forced-nominal-data-misses`
from `development/v1.5.5` at bb3fb9a0. Analysis, fixes, exactness argument
and Lean obligation: docs/DATATYPES.md, "Forced nominal routes: the omission
certificate and the bridge pigeonhole (2026-10-31)".

## Findings

| probe | wrong on (base bb3fb9a0) | cause | fix |
|---|---|---|---|
| `inverse_functional_merge` | `certified_nominals`, `nominals` | the data-ABox omission certificate (`DataAbox::positive_assertions_redundant`) dropped the assertions: its merge closure ignores inverse functionality | accept only one asserted literal per `≤ 1`-bounded property (fb234b4d) |
| `count_with_assertions_ok` | `auto`, `certified_nominals` (bridge arm), forced `ht_bridge` | native bridge: the satisfiable expander cache parked the finite cover of data successors, so no value-singleton merge and no pigeonhole clash | no satisfiable expander cache when the bridge consumes a singleton concept; asserted data bounds above two defer like TBox ones (0520da9d) |

The bridge defect is not specific to assertions: `G ⊑ ≥ 2 u` with
`DataPropertyRange(u xsd:boolean)` and `F ≡ ∃u.{true}` lost `G ⊑ F` on
`auto` (a shipping wrong answer of the automatic route). `probes/` holds the
reduction variants (`v1` to `v7`; `v5b` is the Boolean case); HermiT answers
are cached under `.work/agent-scratch/forced-nominal-data-misses/gold-fixtures`.

Base vs fix on the variants (`runs/fixtures-{base,fix2}.tsv`, routes auto,
certified_nominals, nominals, HermiT gold in `probes/gold/`): base 31 ok, 11
WRONG; fix 42 ok.

| input | base WRONG on | fix |
|---|---|---|
| `v1` (`≥ 3 u` over `{1,2,3}` asserted on `a`, `E ≡ {a}`, `F ≡ ∃u.{3}`) | auto, certified_nominals | ok (bridge defers, CB answers) |
| `v5` (`≥ 2 u` over `{1,2}` asserted) | auto | ok |
| `v5b` (`G ⊑ ≥ 2 u`, `xsd:boolean`, `F ≡ ∃u.{true}`) | auto, certified_nominals | ok |
| `v5g`, `v5e` (TBox `≥ 2 u` over `{1,2}`) | auto, certified_nominals | ok |
| `v6` (`v1` with `∃u.{3} ⊑ F` only) | auto, certified_nominals | ok |
| `v3` (object analogue with nominals), `v1neg`, `v1all`, `v5c`, `v5d` (unsatisfiability forms) | none | ok |

## Binaries

- `km.base`: `engine/target/release/km` at bb3fb9a0 (`cargo build --release -j 12`),
  sha256 `bf211f4cbe44d32d…`.
- `km.fix2`: the same at 0520da9d (the two code commits), sha256 `f2e45d7cf3aa4c53…`.

Both under `.work/agent-scratch/forced-nominal-data-misses/`. Every
differential run pins KM to one CPU (`scripts/one-fix2`: `taskset` on CPUs
44 to 49 claimed by lock files, `KM_THREADS=1`), at most three runs at a time
(`DIFF_THREADS=3`).

## Tests (`tests/`, `--release`, km.fix2 tree)

Integration (`tests/integration.txt`, `--test-threads=3`, `KM_THREADS=1`):
native_data_values 30 passed (the two probes on all three routes, plain and
padded, and the two new fixtures), data_assertions_carried 9, data_range_corners
34, empty_and_universal_data_ranges 10, integral_datatype_difference 3,
data_abox_projection 2, merge_hypotheses 6 passed 1 ignored,
top_nominal_data_successors 16, universal_role_and_top_data_range 12 passed
1 failed: `data_value_singleton_next_to_nominal_successors`, "km classify
exceeded 10s (route nominals)", the object-value case that fails on the base
as well (results/agents/2026-10-31/nominal-exchange/data/tests-targeted.txt)
and that `fix/v155-objvalue-cost` addresses; it fails by time only.

Lib (`tests/lib-*.txt`): `frontend::` 424 passed (includes the new
`omission_certificate_rejects_two_values_whose_owners_may_merge`),
`engine::` 67 passed 1 ignored, `konclude_ht::bridge` 181 passed 7 ignored.
No test fails on this branch that passes on the base.

Lean: `lean/ContextCalculus/DataAboxOmission.lean` compiled with core Lean
v4.30.0-rc2 together with `TwoSortedDL`, `LinearValueEncoding` and
`DataValueProjection` (`lean -o` into the scratch directory, no lake build);
`#print axioms` of `omission_complete`: `propext`, `Classical.choice`,
`Quot.sound`; of `omission_sound`: `propext`; no `sorry`.

## Differential runs against HermiT (`runs/`)

`scripts/drive.sh <tag> <pools>` with `diff_run.py` of
`results/agents/2026-10-30/data-values-3/scripts/`; `scripts/cmp.py NEW OLD`
gives the verdict transitions against the earlier agents' tables.

| pool | files × routes | cap | km.fix2 | earlier table | change |
|---|---|---|---|---|---|
| data probes of `data-values` (`probes`) | 38 × auto, certified_nominals, nominals | 60 s | 103 ok, 11 TIMEOUT, 0 WRONG | km.base (`probes-base.tsv`): 95 ok, 11 TIMEOUT, 8 WRONG | the 8 WRONG rows (both probes) → ok; same timeouts (`count_byte`, `count_finite_range`) |
| reduction variants (`fixtures`) | 14 × 3 | 60 s | 42 ok | km.base: 31 ok, 11 WRONG | see above |
| 2026-10-29 top-nominal-data seeds (`tnd-*`) | 87 × nominals, certified_nominals, auto | 60 s | 224 ok, 37 TIMEOUT, 0 WRONG | data-values-3 dv3f | identical except m2197 nominals and certified_nominals TIMEOUT → ok; the two `sorts_differential` files were ERR there (the fixture paths had moved) and are ok here |
| gen_nomdata seeds m2000-m2399 (`nomdata-forced`) | 400 × nominals, certified_nominals | 30 s | 535 ok, 265 TIMEOUT, 0 WRONG | data-values-3 perf6 (nominals only, 60 s) | 9 TIMEOUT → ok; m2291 ok at 59.4 s there, TIMEOUT at this 30 s cap |
| gen_nomdata seeds m2000-m2399 (`nomdata-auto`) | 400 × auto | 60 s | 380 ok, 20 TIMEOUT, 0 WRONG | data-values-3 perf6 | 17 TIMEOUT → ok, none lost |
| r3-unannounced seeds with data (`r3data-auto`, `nomdata/`) | 300 × auto | 30 s | 281 ok, 19 TIMEOUT, 0 WRONG | no auto table | |
| nominal-r1600 fr seeds with data (`r1600-auto`) | 400 × auto | 30 s | 380 ok, 20 TIMEOUT, 0 WRONG | no auto table | |

Seeds of the 2026-10-29/30 pools without any data construct
(`r3-unannounced/seeds`, `tpl`, `tpl2`) were not rerun: the three changes act
only on data assertions (the omission certificate), on bridge inputs with a
consumed value singleton (the cache) and on nominal assertions over a data
role (the gate), so their inputs reach the same code paths as on the base.

ORE scope (`scope/`, 135 design-half inputs with data assertions, auto,
240 s, three at a time, km.fix2 then km.base): identical exit codes, DROPPED
counts and reference verdict strings on all 135 (and identical to
data-values-3 dv3f); 130 answered by both, 722.5 s against 792.6 s. The
largest per-input ratios (ore_ont_7988, 8595, 9248, 2826, 4572: 2.3 to 3.8)
are load: rerun alternately three times each on one CPU (`scope/pair.tsv`,
`scripts/pair.sh`) they are equal to within 0.03 s.

## Reproduce

    S=.work/agent-scratch/forced-nominal-data-misses
    # build, then copy engine/target/release/km to $S/km.fix2
    scripts/drive.sh fix2 probes fixtures tnd-fresh2 tnd-fresh3 nomdata-forced nomdata-auto r3data-auto r1600-auto
    scripts/scope_run.sh fix2 $S/tools/one-fix2 .work/agent-scratch/data-values/scope/names.txt 3 240

## Not done

- The second-priority CB pigeonhole timeouts (`≥ 256 u.unsignedByte`,
  `≥ 9 u.integer[1,9]` on the forced routes; `count_byte` also on auto) are
  unchanged: an exact cover or counting shortcut needs its own proof and was
  not attempted.
- The Rust-to-`projGate` correspondence of the narrowed certificate is not
  mechanised (as for the projection itself).
- No ORE-wide or Ibex run; the change set touches only data-bearing inputs,
  which the scope set covers.
