# Data values, part 2: defects, ore_ont_7610, QUDT, ore_ont_4572 (agent `data-values-2`)

2026-10-30, branch `fix/v155-data-values-2` off `development/v1.5.5`
(97515f0c after merges). Designs and exactness arguments:

- `docs/DATATYPES.md`: "Fixes of findings 1 and 2" (singleton elision,
  derived string types, exhaustible ranges) and "Functional data values in
  the ABox quotient" (S3);
- `docs/PER-CONTEXT-ORDERING.md` section 10: data-sort marker order, stop at
  a global refutation, empty-head subsumption indexes;
- `docs/DETERMINISTIC-SUBSUMER-SHORTCUT.md`: batched refutation of possible
  subsumers in the bridge.

## Binaries

- `km-v155-final`: the previous agent's LTO build of 0188fcc7 (reference of
  the brief), `.work/agent-scratch/data-values/bin/km-v155-final`.
- `km-devhead`: non-LTO build of development/v1.5.5 at 97515f0c (baseline
  of the paired scope run).
- `km-v155-dv2c`: LTO release build of this branch at 4a53eed6, sha256
  `7b5cdab89818e703…`, in `.work/agent-scratch/data-values-2/bin/`.
- `km-dev13`, `km-dev14`, `km-dev17`: non-LTO builds (line tables) of the
  branch at 581b7fb5, 285ac4e8 and 4a53eed6.

## The eight inputs

`scripts/timing.sh`: `km-v155-final` and `km-v155-dv2c` side by side, one
core each (`KM_THREADS=1`, release flags of `scripts/runone.sh`), 600 s cap
(QUDT 1,800 s), shared workstation (load 30 to 70 on 56 cores during the
day). Audit with the v1.5.3 canonicaliser against the pinned references
(QUDT: `scripts/qudt_cmp.py` against HermiT's 759 subsumptions). Rows:
`timing/final-*.tsv`.

| Input | km-v155-final | km-v155-dv2c | outcome (dv2c) |
|---|---|---|---|
| ore_ont_10425 | 1.46 s | 1.49 s | exact, agrees with Konclude, HermiT, Openllet, JFact |
| ore_ont_15655 | 4.94 s | 5.06 s | exact, agrees with Konclude, HermiT, Openllet |
| ore_ont_5368 | 7.34 s | 1.17 s | exact (ABox quotient), agrees with all four |
| ore_ont_10874 | 3.02 s | 3.04 s | exact, agrees with Konclude, HermiT, Openllet |
| ore_ont_4410 | 18.14 s | 18.43 s | exact, agrees with all four (RSS 2.5 GB, was 1.6 GB) |
| ore_ont_4572 | 400.12 s | 3.21 s | exact (ABox quotient, S3), agrees with Konclude, HermiT, Openllet |
| ore_ont_7610 | timeout 600 s | 54.67 s | exact, inconsistent, agrees with all four |
| qudt-merged | timeout 1,800 s (previous agent's run, `data-values/timing/rc.tsv`) | 108.0 s (RSS 6.3 GB) | exact: consistent, 759 subsumptions = HermiT, DROPPED 0 |

v1.5.4 on QUDT (`.work/pgo-v154/km-pgo-use`, 1,800 s, `qudt/qudt-v154*`):
no answer. It routes the input to `certified_nominals`, cannot convert the
6,124 data-property assertions for the HT arm ("native ABox conversion
declined: 6124 data-property assertion axiom(s) are unsupported", "HT not
routable"), so only the CB stack runs, with those assertions not carried,
and it does not finish within 1,800 s (RSS 0.47 GB at the cap). The
release-note statement that v1.5.4 classifies QUDT correctly but slowly is
not supported by this measurement: it gives no answer, and an answer would
have carried `DROPPED`.

## Item 1: ore_ont_7610

Profile (`scripts/capture.sh`, `scripts/eng.sh` with `KM_PROF`,
`KM_PROF_TIME`, `KM_DUMP_WO`, gdb samples): the nominal CB route spends its
time in backward subsumption of r-Pred arrivals in the ground context. With
the sort encoding (emitted since m2197 for any data property) the
relativized facts `→ C(o) ∨ __data__(o)` kept `__data__(o)` as a
non-maximal literal (the marker had a low concept id), so the ground
context held 46,944 clauses after seeding; with the data assertions it is
49,000 and more. The bridge declines the input at its datatype gate (a blank
data node cannot satisfy `Nematode_Damage ≡ ∀has_factor.Pest_Nematode`), and
the input is inconsistent. Fixes (all in the CB engine/builder, none changes
the calculus): marker last in the concept order from 64 individuals on;
stop the one-shot run at a global refutation; index the empty-head
backward and forward subsumption scans of large contexts (needed after the
merge of the inert-sort release, which otherwise brings 7610 back past
300 s). Timings: base > 600 s; 38 to 64 s with the fixes on the loaded host.

## Item 2: QUDT

Bridge profile (`scripts/bridge-ts.sh`, `KM_BRIDGE_PROGRESS`,
`KM_BRIDGE_TRACE`): satisfiability phase 64 to 106 s (227 subjects);
verification 3,308 s (`qudt/qudt-forced-bridge-pairwise.summary`). Every
subject has 8 to 13 possible subsumers defined by universal restrictions;
the consistency completion leaves 12,090 disjunctions open, so the
precomputation replay is off (`BRIDGE-REPLAY disabled`), and each pairwise
probe re-derives the nominal-connected ABox (28,900 label insertions, 1,764
nodes, 0.35 to 0.85 s). One batched probe `s ⊓ ¬c1 ⊓ … ⊓ ¬ck` per subject
refutes all of them when satisfiable: all 187 batched probes are
satisfiable, one pairwise probe remains, verification 65 s. Forced bridge
146 s (RSS 0.46 GB, was 9 GB), automatic route 156 s
(`qudt/qudt-auto-dev14.stderr`); both equal HermiT's answer. HermiT 1.4.6
takes 2,340 s.

## Item 3: ore_ont_4572

The ABox quotient declined (29,113 blocks of 32,990): its key held the
values of the 28 functional data properties. S3 abstracts the values of an
isolated functional data property to their datatype class when no
construct can tell two values of a class apart or make two individuals
coincide; the quotient then has 4,484 blocks (48,639 assertions) and the
run takes 3 to 12 s. The proof of (1) is the copy construction in
docs/DATATYPES.md. 5368 also gains (quotient accepted, 1.2 s).

## Defects (supervisor items)

- A, singleton elision (`opaque_merge*`): fixed by the `fullyDecided`
  gate and the exact derived-string values; B, range exhaustion
  (`range_exhaust*`): fixed by the exhaustible-range covers. The third item
  (the sort-fixpoint skip of 0188fcc7) was reverted on development by the
  supervisor; this branch contains the revert and does not reintroduce it.
- Lean probe set (`diff/lean-probes-dev13.tsv`, 9 probes × 3 routes): 24 ok,
  3 "WRONG" = `opaque_single` on all three routes, where KM answers
  inconsistent as the OWL 2 datatype map requires (`"abc"^^xsd:token` is the
  string `"abc"`) and HermiT answers consistent although it entails `A ≡ B`
  on `opaque_merge_tbox`, which needs the same equality. The integration
  fixture records the datatype-map answer.
- New wrong answer found, pre-existing in km-v155-final and not fixed:
  `probes/cell_exhaust_tbox.ofn` (`A ⊑ ∃p.(integer[1,9] ⊓ ¬integer[1,8])`,
  `A ⊑ ¬∃p.{9}`): HermiT `A ⊑ ⊥`, KM satisfiable on `auto` and `nominals`,
  no `DROPPED`. A `DataIntersectionOf` with a complement is one opaque range
  name without relations to the values (the "Open corners" item of
  docs/DATATYPES.md); it is not refused.

## Validation

- Integration suites, final code (`diff/itest-dev14.txt`, the 12 data
  suites with the new fixtures): 100 passed, 1 failed, 1 ignored. The failure
  is `data_value_next_to_universal_role_hub_stays_satisfiable` (10 s bound,
  automatic route): the development head itself takes 9.6 s on it alone
  (`probes/hub_data.ofn`, km-devhead 9.6 s, this branch 9.9 s; e62a4bce 1.4 s),
  so the bound is exceeded under load on both.
- Bridge, HT and nominal suites (`diff/itest-bridge-dev14.txt`, 23 suites):
  91 passed, 0 failed, 1 ignored.
- Library unit tests (`diff/unit-all-*.txt`): development head 3,025 passed,
  31 failed; branch 3,028 passed, 31 failed; branch with
  `KM_ACTIVE_BODY_INDEX_MIN=1` (indexes in every context) 3,029 passed,
  30 failed. The branch's failures that the head does not show
  (`elcomplete::…reflexive_role_composes_with_chain`, `qopc_transitive_chain`,
  `qosat_edge_index_role_chain`) pass alone; the head's own set contains
  other `elcomplete` tests that vary from run to run.
- Data probes of the previous agent (`diff/probes-*.tsv`, 19 probes plain and
  padded, 3 routes, 120 s): 97 ok, 6 WRONG, 11 TIMEOUT on km-dev13; the wrong
  ones are the pre-existing `inverse_functional_merge` (nominal CB routes)
  and `count_with_assertions_ok` misses. `count_with_assertions_ok` on
  `certified_nominals` alternates between ok and WRONG from run to run with
  km-v155-final as well (a race between the correct HT arm and the
  incomplete CB arm).
- Nominal-data seeds (`diff/seeds/`, 87 files × 4 routes, 60 s): no WRONG
  on km-dev10, km-dev13 or km-dev17 with `KM_ACTIVE_BODY_INDEX_MIN=1`.
  Against the 2026-10-30 baseline (`data-values/diff/top-nominal-data/*-p10`)
  the only changes are timeouts that now answer (m2058 auto and
  certified_nominals, m7022, m7048, m7101, m7178) and `m2222` on
  `certified_nominals` (0.0 s alone with both binaries).
- Scope: the 135 design-half inputs with data assertions
  (`scope/*.tsv`, 240 s, 4 in parallel). Paired with km-devhead:
  km-dev13 130 verified → 130 verified, median ratio 1.000, mean 1.010;
  km-dev14 (batched refutation) and km-dev17 (indexes), run later at lower
  load: 130 → 130, no wrong answer, total 1,407 s → 1,126 s and 751 s.
  4572 and 5368 move to the ABox quotient, 3561 to the bridge.

## Not done

- No Lean model for the quotient (S1 to S3), the bridge batching, the
  oracle's derived-string decisions or the cover condition; the engine and
  bridge changes are scheduling and redundancy-index changes with no Lean
  obligation (arguments in the docs).
- `cell_exhaust_tbox` (above) is not fixed.
- The scope and timing runs are on the shared workstation, not on Ibex.

## Reproduction

`scripts/` expects `.work/agent-scratch/data-values-2/` with links
`inputs`, `refs`, `v153tools` to `.work/agent-scratch/data-values/`.
