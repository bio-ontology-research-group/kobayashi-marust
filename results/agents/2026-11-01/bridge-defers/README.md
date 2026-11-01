# Native bridge defers on ore_ont_4903 and ore_ont_11647 (agent `bridge-defers`, 2026-11-01)

Branch `fix/v155-bridge-defers` from `development/v1.5.5` (1427ce55),
worktree `.work/worktrees/fix-bridge-defers`. Release flags on every
measurement (`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`,
`--lines`, `timeout 240`). Base binary: the RC
`.work/pgo-v155/km-v1.5.5-rc-pgo`. Branch binary: plain release build of
the branch (no PGO).

## Why the bridge deferred

Both inputs declined at the bridge's datatype gate, before any completion
structure was built. Three gates applied in turn. Each one became visible
only after the previous one was fixed, and the defer message now names
each of them.

| input | gate 1 (both) | gate 2 |
|---|---|---|
| 4903 | pure datatype relation clause not exact: `decimal[-250,-150] → decimal(-250,-150) ∨ {-150} ∨ {-250}` | per-group decimal cell path: "a decimal-tower vocabulary has a label set without two realizing values" (the path read only integral covers) |
| 11647 | pure datatype relation clause not exact: `decimal(<12) → {0} ∨ {3} ∨ decimal(<0) ∨ decimal(0,3) ∨ decimal(3,12)` | IEEE certificate: "an IEEE facet vocabulary has a label set without two realizing values" (83 `xsd:float` ranges on `muo:numericalValue`; the certificate enumerates label subsets and gives up above 16 ranges) |

Gate 1 is the ordered-cell cover that the frontend emits for a role group
with a dense decimal range. `pure_datatype_relation_is_exact` knew only the
integral, union, enumerated, finite and IEEE covers. Neither input has a
problem with nominals, `XMLLiteral`, inverses or cardinalities on the
bridge: after the three datatype gates both run through the native nominal
path unchanged.

Defer messages before and after (forced `--route ht_bridge`):

    base:  unsupported: selected native HT bridge deferred (konclude_ht bridge defer)
    fix1:  ... (konclude_ht bridge defer: datatype gate: a decimal-tower vocabulary has a label set
           without two realizing values (group [...]))                                  [4903]
    fix1:  ... (konclude_ht bridge defer: datatype gate: an IEEE facet vocabulary has a label set
           without two realizing values)                                                [11647]

(`fix1` = the cover check alone; `data/runs/*-forced-*.err`.) On the
automatic route the HT worker's stderr, with this message, is visible under
`KM_HT_STATS=1`.

## What changed (commit f5935a5e and the follow-up docs/test commit)

1. `frontend::datatypes::bridge_exact_decimal_cell_cover` (a bridge-only
   oracle function; the frontend does not call it) decides `R → H₁ ∨ … ∨ Hₖ`
   over the decimal tower. It cuts the line at every endpoint and head
   value; the pieces are the cut points plus the integers and the
   non-integer decimals of each open gap; one representative per piece.
   It refuses `owl:rational`/`owl:real` and other families, and returns
   `false` on any undecided membership. The bridge accepts the clause in
   `pure_datatype_relation_is_exact`.
2. `decimal_cells_exact` feeds these covers to its existing per-group cell
   path, as it already did for integral covers.
3. `frontend::datatypes::bridge_ieee_cells_by_atoms`: a cell path for one
   IEEE width over **all** its ranges (not per group). It applies only when
   every non-atomic range has a present `bridge_exact_ieee_cell_cover` whose
   range heads are atomic, and is skipped when a complement of the width is
   present; otherwise the enumeration runs as before.
4. Defer reasons: a thread-local note in `konclude_ht/bridge.rs`, set by
   the datatype gate (every `defer!` and every formerly print-only exit,
   with concept names), by the input gates, the encoder, and the
   prepare/classify exits, plus a phase milestone. The three bridge entry
   points in `tableau.rs` read it into `konclude_ht bridge defer: <reason>`.
   It is diagnostic only and never changes a verdict.

Exactness arguments: docs/DATATYPES.md, "Native bridge: dense decimal cell
covers" (cover validity by the piece argument; why feeding valid covers to
the cell path keeps its argument; the IEEE atom argument: an atomic range
lies inside or outside each other range because the relation clauses are
valid, so a label that holds an atomic `C` is fixed by the clauses, and any
value of `C` realizes it in both directions). The bridge has no Lean model;
these are paper arguments plus the differential evidence below.

Frontend files touched: `frontend/datatypes.rs` (two new bridge-only
functions plus tests) and `frontend/datatypes/vocabulary.rs`
(`noninteger_between` made `pub(super)`, new `decimal_value`). No clause
generation changed. `km ofn` output is byte-identical between the base RC
binary and the branch on 1,382 inputs: the 300 decimal and 200 float seeds,
the 400 data-coverage and 400 nominal-coverage seeds, 80 small ORE inputs
with numeric datatypes, and 4903 and 11647 (`data/frontend-identity.txt`,
`tools/frontend_identity.sh`).

## The two inputs

| input | route | base | branch | references |
|---|---|---|---|---|
| 4903 | auto | timeout 240 s | 112.7 s, 12,121 SUB, 0 UNSAT, 203 MB | Konclude: agreement (the only completed complete reference) |
| 4903 | ht_bridge | exit 3 at 0.2 s | 95.4 s, 219 MB | |
| 11647 | auto | timeout 240 s | 6.8 s, 264 SUB, 252 MB | Konclude, HermiT, Openllet: agreement |
| 11647 | ht_bridge | exit 3 at 0.5 s | 4.5 s, 304 MB | |

The comparison uses the audit's canonicalizer and `compare_taxonomies.compare`
against `v150-refs/classification-audit-53234885/{39/ore_ont_4903,7/ore_ont_11647}`
(`tools/compare_ref.py`, `data/reference-agreement.jsonl`).

4903 is within the protocol but far from Konclude's 0.5 s: the bridge
spends 67 s preparing 1,875 subjects and 27 s verifying candidates
(`BRIDGE-SAT-PHASE` in `data/runs/fix2-forced-4903.err`). On auto the
bounded bridge-first attempts decline within their budget, and the
`certified_nominals` race answers through its HT worker at 99.7 s. That
remaining gap is a cost problem in the bridge's probes, not an admission
problem.

**The exact nominal CB stack alone** (forced `--route nominals`, base
binary): it times out on both within 240 s. 4903 reaches 7.1 GB RSS and
11647 1.1 GB, with no answer (`data/runs/base-nominals-*.err`). On these
inputs it is a cost problem, not a missing construct. I did not
investigate it further (the CB calculus is out of scope).

## Differential (HermiT 1.4.6 gold, 60 s per run, 2 runs at a time)

`tools/run_pools.sh` / `tools/diff_run.py` (copied from
`data-coverage-regression`); rows in `data/diff/<pool>.<before|after>.tsv`.

| pool | route | base ok / WRONG / REFUSED / TIMEOUT | branch ok / WRONG / REFUSED / TIMEOUT |
|---|---|---|---|
| dec (new, 300) | ht_bridge | 108 / 0 / 192 / 0 | 147 / 0 / 153 / 0 |
| dec | auto | 299 / 0 / 0 / 0 (+1 DROPPED) | 299 / 0 / 0 / 0 (+1 DROPPED) |
| flt (new, 200) | ht_bridge | 0 / 0 / 200 / 0 | 155 / 0 / 45 / 0 |
| flt | auto | 43 / 0 / 0 / 157 | 163 / 0 / 0 / 37 |
| data-coverage-regression (400) | ht_bridge | 24 / 0 / 376 / 0 | identical |
| nominal-coverage (400) | ht_bridge | 113 / 0 / 287 / 0 | identical |
| data-values probes (38) | ht_bridge | 25 / 0 / 13 / 0 | identical |
| forced-nominal-data-misses fixtures (14) | ht_bridge | 7 / 0 / 7 / 0 | identical |
| top-nominal-data fresh3 (200) | ht_bridge | 55 / 0 / 145 / 0 | identical |
| bridge-nominal-merge (2000) | ht_bridge | 1,993 / 0 / 7 / 0 | identical |

0 WRONG anywhere, before or after. The only verdict changes are REFUSED → ok
(39 dec, 155 flt on ht_bridge) and TIMEOUT → ok (120 flt on auto), each
equal to HermiT. Both newly admitted constructs have a generated family
with HermiT gold: `tools/gen_decimal_cells.py` (dense decimal covers with
open gaps, closed and half-bounded intervals, `DataIntersectionOf` of two
facets, integer values, nominals) and `tools/gen_float_cells.py` (17 to 22
float ranges on one property, as in 11647; one seed in five uses two
properties, whose cells overlap across groups, so the by-atoms path
declines and those seeds stay refused). Seeds and gold:
`data/seeds-and-hermit-gold.tar.gz`. The remaining 198 dec/flt bridge
refusals and their named gates (`data/refusal-reasons.txt`): 88 dec "a
datatype symbol is not in the exact atomic map" (mostly decimal band cells
`DataIntersectionOf(… DataComplementOf(xsd:integer))`), 45 flt "an IEEE facet
vocabulary has a label set without two realizing values" (two float
properties whose cells overlap across groups, more than 16 ranges), 29 dec
"a datatype existential conflicts with its role range", 13 dec "an extension
datatype pair has no exact decided relation", 10 dec "a local datatype
restriction has an undecided relation", 6 dec "nominal metadata is not
covered", 2 + 2 dec other datatype gates. Three more dec seeds are refused
before the bridge by the orchestrator ("native HT bridge ABox conversion
was incomplete").

## Tests (`KM_THREADS=1`, `--test-threads=1`, release)

- `cargo test --release --lib`: 3,106 passed, 21 failed, 10 ignored. The
  21 failures are exactly the checker-bound baseline at 1427ce55: 20
  `tableau::` tests plus
  `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`
  (`data/lib-failures.txt`). No other test fails. The six new unit tests
  (`frontend::datatypes::decimal_cell_cover_tests::*`,
  `frontend::datatypes::ieee_cells_by_atoms_tests::*`) pass.
- Every integration target (`engine/tests/*.rs`, 86 targets, each run
  separately): all pass, 472 tests, 0 failed
  (`data/tests-integration-summary.txt`).

## Not done

- 4903's bridge time (95 s against Konclude's 0.5 s) is unchanged; the
  probes, not admission, dominate.
- The per-group decimal cell path keeps its existing argument; I did not
  re-derive it beyond checking that a valid cover cannot break it.
- Decimal band cells (`… DataComplementOf(xsd:integer)`) and IEEE cells
  that overlap across role groups remain deferred.
