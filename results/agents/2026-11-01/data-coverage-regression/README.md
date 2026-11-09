# data-coverage-regression: dateTime bounds and XMLLiteral values (v1.5.5)

Agent `data-coverage-regression`, branch `fix/v155-data-coverage-regression`
off `development/v1.5.5` at 775223bf. Design, exactness argument and Lean
obligation: `docs/DATATYPES.md`, "dateTime bounds and XMLLiteral values
(2026-11-01, agent `data-coverage-regression`)" and the open corners table.

## Defect

The S1 preview of 775223bf lost two held-out inputs that v1.5.3 answers
and verifies: `ore_ont_13077` (`DROPPED 1`, a dateTime `minExclusive`
bound) and `ore_ont_13584` (`DROPPED 18`, `rdf:XMLLiteral` literals).
v1.5.3 answered both with the free abstraction (bound and literals related
to nothing); v1.5.5's decided fragment reported them.

## Fix

- `frontend/datatypes/time.rs`: the `xsd:dateTime` value space as two axes
  (instants of timezoned values, local times of untimezoned values) with the
  XSD 1.1 order and the fourteen-hour rule; `DRange::Time` facet intervals;
  ordered cells for the dateTime family (`vocabulary::time_cells`).
- `rdf:XMLLiteral`: `Val::Xml(lexical form)` for literals in exclusive
  canonical form (text and elements without attributes or prefixes),
  identity by lexical form; conformance rejects decidedly non-canonical
  forms (exit 2); markup outside the fragment stays reported.
- Lean: `lean/ContextCalculus/DataRangeDateTime.lean` (no `sorry`).

## Binaries

| name | source | sha256 prefix |
|---|---|---|
| head (preview) | `.work/pgo-v155-preview/km-v1.5.5-rc-pgo`, 775223bf PGO | 5cd65bba66e43133 |
| v1.5.3 | `.work/v153-release-assets-b5abf83a/km-v1.5.3-linux-x86_64` | 2470b0415f1a7853 |
| `km-dcr2` | this branch, `cargo build --release --bin km` (`.work/agent-scratch/data-coverage-regression/bin/km-dcr2`) | c36ae86847e1de1c |

Release flags for every run on ws: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`, `classify --lines`.

## 13077 and 13584 (auto route)

| input | head 775223bf | v1.5.3 | branch `km-dcr2` |
|---|---|---|---|
| ore_ont_13077 (held-out) | DROPPED 1 | DROPPED 0 | DROPPED 0, taxonomy byte-identical to v1.5.3 (359 SUB) |
| ore_ont_13584 (held-out) | DROPPED 18 | DROPPED 0 | DROPPED 0, taxonomy byte-identical to v1.5.3 |

The 18 literals of 13584 are canonical (text without `&`, `<`, `>`, CR).

## Pool sweep (item 3)

`scripts/sweep.py`: every input of the 1,708-input pool
(`.work/v152-correctness-1920/full-candidate-inputs-ws.json`,
`input_admission = checks_passed`), line mode, 240 s (`timeout -s KILL`),
`prlimit --as=20 GiB`, `taskset` to one CPU each, 3 in parallel, on ws (load
15 to 18 from other agents during the run).

- head (`sweep/head-775223bf.jsonl`, 1,708 records): 1,660 `DROPPED 0`,
  2 `DROPPED > 0` (13077, 13584), 46 without an answer (45 timeouts, ore_ont_8250
  refused with exit 3: DL-safe rules through a nominal).
- v1.5.3 on the 48 head inputs with `DROPPED > 0` or no answer
  (`sweep/v153.jsonl`). An input with head `DROPPED 0` cannot be on the list,
  so v1.5.3 was not run on the other 1,660; the list is the same as with a
  full v1.5.3 sweep.
- branch on the listed inputs (`sweep/branch-dcr2.jsonl`).

Inputs where the head has `DROPPED > 0` and v1.5.3 `DROPPED 0`
(`sweep/compare.md`):

| input | half | head | v1.5.3 | branch |
|---|---|---|---|---|
| ore_ont_13077 | held-out | DROPPED 1 | DROPPED 0 | DROPPED 0 |
| ore_ont_13584 | held-out | DROPPED 18 | DROPPED 0 | DROPPED 0 |

Before: two, both held-out. After: none on either half.

Head timeouts. Nine head timeouts are answered by v1.5.3 within 240 s on
ws: 10949, 15803, 16744, 3215, 7246, 7507, 8737 (design) and 345, 9027
(held-out). None of them is a data corner: a 90 s classify with
`KM_DT_AUDIT=1` (`scripts/audit_check.sh`, `sweep/audit-head-noanswer.txt`)
prints no undecided datatype name for any of the 46 head inputs without an
answer except ore_ont_11647 (design), where the head reports 105 undecided
`rdf:XMLLiteral` markup literals (`<sub>`, `<sup>`, `<i>`); v1.5.3 also times
out on 11647, and the branch reports none (`undecided=0`). The branch
answers 10949, 15803 and 3215 within 240 s and times out on the other six
like the head; 9027 is also a held-out timeout of the Ibex preview
(`.work/v155-preview-assets/BENCHMARKS.md`), and 345 answers in 2.7 s on
Ibex. These are time losses for the S1 owners, not `DROPPED` corners.

XMLLiteral rejection: the seven pool inputs that mention `rdf:XMLLiteral`
(11647, 1618, 13584, 178, 385, 13132, 1342) pass the branch frontend's
conformance (`km ofn` exit 0), so the canonical-form check rejects no pool
input.

## Fixtures and probes (HermiT 1.4.6 gold)

- `engine/tests/fixtures/data_range_corners/`: ten new fixtures
  (`datetime_zone_mix_out`, `datetime_zone_mix_in`,
  `datetime_zone_subsumption`, `datetime_zone_empty`, `datetime_point_cells`,
  `datetime_cells_helly`, `datetime_untimezoned`, `xml_literal_identity`,
  `xml_literal_distinct`, `xml_literal_string`); the three earlier dateTime
  probes (`datetime_empty`, `datetime_value`, `datetime_subsumption`) moved
  from `declined` to `exact`. `diff/fixtures-new.tsv`: all ok on `auto`,
  `certified_nominals`, `nominals` (also six HermiT probes `hprobe/h*`).
- data-values-3 probes (`diff/dv3-probes-new.tsv`, 35 × 3 routes): 78 ok,
  3 WRONG (the recorded `string_chain` datatype-map answer), DROPPED/REFUSED
  only for pattern, length and `HasKey` probes, 3 NOGOLD (`nary_some`); the
  base had the three dateTime probes DROPPED/REFUSED.
- 400 generated seeds (`scripts/gen_seeds.py`, 200 `dt` + 200 `xml`; seeds
  and gold in `seeds/seeds-and-hermit-gold.tar.gz`), 60 s, routes `auto`,
  `certified_nominals`, `nominals`, `ht_bridge`:

  | binary | route | ok | WRONG | DROPPED | REFUSED |
  |---|---|---|---|---|---|
  | branch `km-dcr2` | auto | 399 | 0 | 1 | 0 |
  | | certified_nominals | 399 | 0 | 0 | 1 |
  | | nominals | 399 | 0 | 0 | 1 |
  | | ht_bridge | 24 | 0 | 0 | 376 |
  | head 775223bf | auto | 47 | 0 | 353 | 0 |
  | | certified_nominals | 46 | 0 | 0 | 354 |
  | | nominals | 46 | 0 | 0 | 354 |
  | | ht_bridge | 12 | 0 | 0 | 388 |

  The branch's one DROPPED (`xml0023`, a duplicated `ClassAssertion`) and
  the two REFUSED rows (`xml0024`, a class-only ontology: "positive EL ABox
  consistency certificate declined") have no data cause. `ht_bridge`
  refuses the dateTime facet and XMLLiteral names by design (the bridge's
  exact map does not admit them).

HermiT differs from XSD 1.1 on midnight: it counts `T24:00:00` as a value
of its own (`DateTimeInterval.subtractSizeFrom`), so the probes avoid
midnight and zero seconds and use at most three fractional digits.

## Tests (`cargo test --release`, `TMPDIR` in the scratch directory)

- `--lib -- frontend::`: 432 passed, 0 failed, 0 ignored
  (`tests-lib-summary.txt`).
- integration (`--test-threads=3`, `tests-integration-summary.txt`):
  data_abox_projection 2/2, data_assertions_carried 9/9, data_range_corners
  44/44, empty_and_universal_data_ranges 10/10, integral_datatype_difference
  3/3, native_data_values 30/30, top_nominal_data_successors 16/16,
  universal_role_and_top_data_range 12 passed, 1 failed:
  `data_value_singleton_next_to_nominal_successors` (case "object value
  instead of data value", route `nominals`, exceeds the 10 s bound). The
  case has no data value; the head PGO binary also runs past 30 s on it
  (`diff/urt-objvalue.ofn`), so the
  failure is not caused by this branch.

## Lean

`lean/ContextCalculus/DataRangeDateTime.lean`, imported by
`lean/ContextCalculus.lean`; `lake build ContextCalculus` succeeds (8,657
jobs). `lean/axioms.txt` (from `lean/print-axioms.lean`): every theorem
depends on at most `propext`, `Classical.choice`, `Quot.sound`;
`xml_value_eq_iff` on none; no `sorryAx`.

## Reproduce

    S=.work/agent-scratch/data-coverage-regression
    python3 $S/sweep.py LABEL BIN OUTDIR [NAMES]          # pool sweep
    python3 -I scripts/compare.py head.jsonl v153.jsonl branch.jsonl
    python3 -I scripts/gen_seeds.py seeds dt 200; python3 -I scripts/gen_seeds.py seeds xml 200
    ls seeds/*.ofn | xargs -P 3 -n 1 scripts/gold.sh ORACLE_DIR GOLD_DIR
    DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 python3 -I scripts/diff_run.py \
      KM .work/agent-scratch/data-values/oracle GOLD out.tsv auto,certified_nominals,nominals,ht_bridge seeds/*.ofn

