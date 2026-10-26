---
name: project_km_datatypes
description: "Datatype reasoning LANDED (1e168e4): data-property axioms un-dropped (Functional -> 6999 unsat FIXED, byte-equal gold) + pairwise concrete-domain oracle (frontend/datatypes.rs); sweep 6006 (res_dt_*) + nominal A/B (res_nom_ab) validating; built on unimatrix ~/km-build (ws DOWN)"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**2026-06-12 LANDED (commit 1e168e4)** — the datatype phase of the SROIQ+
datatypes goal. Two frontend layers, no calculus change:

1. **Axiom translation** (parse.rs): ALL `Data*` axioms were dropped before.
   Now: FunctionalDataProperty → FunctionalRole (THE 6999 fix:
   `=2 affc2 ⊓ Functional(affc2)` unsat; 6999 now **byte-equal to gold**),
   Sub/Equivalent/DisjointDataProperties → role axioms, DataPropertyRange →
   ∀p.__dt__D, DatatypeDefinition → equivalence. Unqualified data
   cardinalities: ⊤ filler (old `__dt__val` filler undercounted — ≤n was
   blind to DataHasValue successors). Soundness hardening: complex ranges
   keyed by canonical text (shared `__dt__opaque` could INVENT subsumptions);
   typed literals re-glued (`"v"` + `^^xsd:int` are split by the tokeniser —
   same-lexical different-type values collapsed, another latent unsoundness).
2. **Pairwise oracle** (frontend/datatypes.rs, ~700 lines + 5 tests):
   classifies occurring `__dt__` names (named type / `__dt__val__<lit>` /
   `__dt__c__<canonical text>`), decides per OWL 2 datatype map: value
   membership, value (in)equality (exact i128 rationals: decimal tower +
   dyadic float/double + specials; strings+lang; booleans), range
   subsumption/disjointness (integer-tower bounds, string tower, partition
   disjointness, interval separation), finite covers (boolean/DataOneOf/small
   int intervals, cap 8) enabling finite-range counting via engine equality.
   Unknown → emit nothing (degrades to the old sound abstraction; pattern
   facets, dateTime arithmetic stay opaque). `KM_NO_DATATYPES` disables the
   oracle pass only (Phase-1 axioms unconditional).

**Validation in flight**: sweep 6006 (`res_dt_*.jsonl`, `ore_out_dt`,
binaries `~/bench/km/{ofn-dt,kobayashi-marust-p2}` = datatypes +
chain-domain-default + nominal-Phase-2 engine) + nominal A/B
(`~/bench/nomab.sh`, KM_NOMINALS=1 over the ~60 gold-comparable nominal onts,
`res_nom_ab.jsonl`, `ore_out_nom`).

**Infra notes**: ws went UNREACHABLE 2026-06-12 ~16:00 (after the load-490
runaway-A/B episode; 39 stale engines killed first). Fallback build host =
**unimatrix01 head node**: rustup installed (`~/.cargo`), source at
`~/km-build/engine`, `MOOSE_HOME=~/sroiq-img/moose` needed for owl_classify.
Binaries built there run on the cluster nodes (generic x86-64). owl_classify
deployed to ~/bench/km/py (stdin-race fix; backup .bak.predt).

OPEN datatype corners (sound, possibly incomplete): pattern/length facets,
dateTime ordering, float/double vs decimal cross-tower subsumption,
DataComplementOf/Intersection/Union structure, n-ary DataSomeValuesFrom,
DataPropertyAssertion ABox under KM_NOMINALS, HasKey.
