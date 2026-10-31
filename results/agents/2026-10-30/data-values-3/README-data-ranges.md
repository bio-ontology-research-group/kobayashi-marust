# Data values, part 3: Boolean ranges, ordered cells, the corners (agent `data-values-3`)

2026-10-30/31, branch `fix/v155-data-values-3` (off development/v1.5.5 at
e2d5dd1f, merged with 6c48c72e and 0e1bd99a). Design, exactness argument and
Lean obligation: `docs/DATATYPES.md`, "Boolean data ranges and ordered cells
(2026-10-30, agent `data-values-3`)" and the "Open corners" table after it.
Item 2 (cost regressions) is on the sibling branch
`fix/v155-data-values-3-perf`, results in `README.md`, `timings.md` and
`tests.txt` of this directory on that branch.

## Binaries (`.work/agent-scratch/data-values-3/bin/`, `cargo build --release --bin km`)

| name | source | sha256 prefix |
|---|---|---|
| `km-base-0e1bd99a` | development/v1.5.5 at 0e1bd99a (paired base) | c5c6bbe2b5f144d6 |
| `km-base-6c48c72e` | development/v1.5.5 at 6c48c72e (base of the probe tables) | 701b703f68c155c8 |
| `km-dv3f` | this branch at 64ab0424 (scope, seeds, nominal-data runs) | d7148a8f2bf4275b |
| `km-dv3g` | this branch at 20057f0f (final; probes, tests) | 5ce5f7c80809d861 |

20057f0f differs from 64ab0424 only in the bridge's acceptance of IEEE cell
covers and a unit test; no scope input and no seed has an IEEE facet.

## Probes (`probes/`, HermiT 1.4 answers in `gold/`)

32 probes for the corners, 3 routes (`auto`, `certified_nominals`,
`nominals`), 60 s, `scripts/diff_run.py`:

    DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 python3 -I scripts/diff_run.py KM \
      .work/agent-scratch/data-values/oracle gold diff/probes-TAG.tsv \
      auto,certified_nominals,nominals probes/*.ofn

| binary | ok | WRONG | DROPPED | REFUSED |
|---|---|---|---|---|
| base 6c48c72e (`diff/probes-base.tsv`) | 18 | 66 | 3 | 12 |
| km-dv3g (`diff/probes-dv3g.tsv`) | 66 | 3 | 8 | 22 |

The 3 WRONG rows of km-dv3g are `string_chain` on the three routes: KM answers
the XSD 1.1 datatype-map answer (`xsd:language ⊑ xsd:NCName`, so `A`
unsatisfiable); HermiT answers `A` satisfiable. The integration fixture
records the datatype-map answer. DROPPED (automatic route) and REFUSED
(forced nominal routes) are the pattern, length and dateTime facet probes
and the two data `HasKey` probes (refused on every route). `nary_some` has no
gold (the OWL API does not parse it); KM rejects it with exit 2 on every
route.

Lean probe set (`../lean-data-values/probes`, 9 × 3): 24 ok, 3 WRONG =
`opaque_single` (datatype-map answer by supervisor decision), on the base and
on every branch binary (`diff/lean-*.tsv`).

## Validation

- Previous agents' 19 data probes plain and padded (38 files × 3 routes,
  120 s): base 6c48c72e and km-dv3c 96 ok / 11 TIMEOUT / 7 WRONG, identical per
  file and route (`diff/data-probes-*.tsv`; the WRONG rows are the
  pre-existing `inverse_functional_merge` and `count_with_assertions_ok`);
  km-dv3g identical as well (`diff/data-probes-dv3g.tsv`).
- Scope (135 design-half inputs with data assertions, 240 s, one stream per
  binary, both side by side, `scripts/scope_run.sh`, `scope/*.tsv`): base
  0e1bd99a and km-dv3f both 130 verified, identical verdict strings, routes and
  DROPPED counts on all 135; total over the 130 676.3 s → 673.1 s,
  median ratio 1.000, mean 1.037. (An earlier branch binary, km-dv3c, lost
  ore_ont_5964: decimal cells took it out of the native bridge's map; fixed by
  64ab0424 and 5a8280de.)
- Nominal-data seeds (87 files × 4 routes, 60 s, `scripts/tnd_run.sh`,
  `diff/diff-*-{base0e,dv3f}.tsv`): base 212 ok / 43 TIMEOUT / 93 ERR, dv3f
  216 ok / 39 TIMEOUT / 93 ERR, no WRONG; the ERR rows are the same
  (`ht_general` refusals). Changes: m2030, m2345, m7100, m7106, m7122 on auto
  TIMEOUT → ok; m2197 on nominals ok (52.6 s) → TIMEOUT, the merge-hypotheses
  cost reported by the perf branch (0.57 s before the r1600 merge).
- Seeds 2000–2399 (gen_nomdata `--no-inverse`, automatic route, 60 s,
  `seeds/seeds-*.tsv`): base 0e1bd99a 366 ok / 34 TIMEOUT, km-dv3f 375 ok /
  25 TIMEOUT, 0 WRONG. Gained m2009, m2023, m2030, m2100, m2123, m2205,
  m2255, m2287, m2311, m2345, m2394; lost m2278, m2359 (29 s and 25 s on the
  base under load; alone with `KM_THREADS=1` 40.1/39.9 s and 32.6/35.3 s on
  base/branch).
- Bridge defer reasons for the 26 seeds of `nominal-seeds/remaining-33.tsv`
  with the complement or singleton defer, forced `ht_bridge`
  (`seeds/defer-ht_bridge.tsv`): none defers on the complement map or the
  singleton gate any more; 2 are admitted, the others defer on other gates
  (blank data node, role-local fragment, complex subclass axiom on data
  nodes, nominal assertions), outside this item.
- Frontend audit (`audit/`): `KM_DT_AUDIT=1 km ofn` on the 83 corpus files
  with complex data ranges plus the 135 scope inputs: one input reaches the
  new DROPPED gate, ore_ont_13077 (a dateTime facet).
- Integration suites (`diff/itest-dv3f.txt`; the 12 data suites and the new
  `data_range_corners`, 13 test files): 132 passed, 3 failed, 1 ignored. The failures are the
  base's: `top_nominal_data_successors::hermit_answers_on_every_route` (m2197,
  merge hypotheses), `universal_role_and_top_data_range::
  data_value_singleton_next_to_nominal_successors` (merge hypotheses) and
  `data_value_next_to_universal_role_hub_stays_satisfiable` (fixed on the perf
  branch). Final source (km-dv3g, `diff/itest-dv3g.txt`): the same counts and failures.
- Library tests `frontend::` and `konclude_ht::bridge`: 604 passed, 0 failed,
  7 ignored (km-dv3g source).

All runs on the shared workstation (load 60 to 140 on 56 cores), not on Ibex.
