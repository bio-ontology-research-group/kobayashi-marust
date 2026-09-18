# Atomic ABox and incremental publication correction

The benchmark controls exposed two independent failures in v1.4.0. Automatic
classification projected `A(a), B(a)` to separate class satisfiability queries,
which cannot detect `DisjointClasses(A B)`. Incremental publication could ignore
a frontend global inconsistency flag. Both could publish `consistent: true`.

The correction rejects atomic projection when one individual has distinct
asserted classes. A single overall asserted class remains admissible, including
repeated assertions and aliased individual names. With several classes, the
screen additionally requires absolute, unescaped individual IRIs to avoid
treating different spellings of one name as independent individuals. A declined
projection keeps the complete ABox on the existing reasoning path. Incremental
publication now combines the frontend inconsistency flag with its existing
asserted-unsatisfiable check and clears taxonomy fields when either is true.

## Experimental order

Proof development began only after these observations:

- The original mapper failed the added fresh-source consistency regression.
- The corrected source-incremental release tests passed: 19 tests.
- The corrected frontend tests passed: 179 tests. One old optimization fixture
  was adjusted to use separate absolute individual names; its old same-name,
  multiple-class assertions no longer satisfy the optimization's premise.
- The parent benchmark task independently compared corrected incremental and
  explanation controls with HermiT/JFact. Their run receipts remain benchmark
  evidence, separate from this proof.

The local logs are under the root `.work/logs/dynamic-abox-*` directory. The
release report must retain the actual remote receipts and source/binary hashes;
these prose statements do not replace that evidence.

## Theorems and implementation correspondence

`ContextCalculus/KMAtomicABoxPublication.lean` proves:

- `singleClass_of_oneClass`: the single-overall-class shortcut is valid without
  assuming distinct individual names.
- `conflicting_rows_decline`: two different asserted classes on the same
  semantic individual contradict the required single-class condition.
- `singleClass_map_of_injective`: the lexical condition transfers to semantic
  identifiers if the accepted individual-name interpretation is injective.
- `atomicSatisfiable_of_singleClass`: construct an actual joint model by finite
  disjoint unions of class models. The construction uses the per-individual
  condition whenever two rows name the same individual.
- `atomicSatisfiable_iff_classes`: under TBox satisfiability and closure under
  disjoint union, the screened atomic ABox is consistent exactly when all its
  asserted classes are satisfiable.
- `nativeAtomic_fullSatisfiable` and `nativeAtomic_taxonomy_exact`: transport the
  constructed witness to the existing native-ABox semantics and taxonomy
  projection theorem. Full consistency is established, not assumed.
- `publish_frontend_false`: the new mapper is identical to the old mapper when
  the frontend flag is false, including the asserted-unsatisfiable branch.
- `publish_frontend_clash`: a true frontend flag suppresses every worker verdict
  and both taxonomy payloads while preserving the dropped count.
- `publish_consistent_iff`: the changed consistency formula is exact for the
  current source if both clash detectors are sound and the worker is exact when
  neither detector fires.
- `direct_disjoint_assertions_inconsistent`: the three clauses corresponding
  to the reproduced disjoint-class assertion clash make any source containing
  them inconsistent. This proves the particular detector premise semantically.

The models represent individual identities, not a unique-name assumption:
different names may denote the same object. The constructed model is free to
assign distinct witnesses because the accepted ABox has no equality, inequality,
role, complex-class, or nominal constraints on those names.

## Explicit proof boundary

The module does not extract or verify the Rust parser, the HashMap screen, the
IRI lexer, or all frontend inconsistency detectors. The implementation must
still provide complete atomic assertion coverage, bind accepted individual and
class identifiers to their source meanings, and establish disjoint-union closure
for the admitted TBox fragment. The existing connected-clause closure theorem
can discharge the mathematical closure condition for an accepted normalized
source. The frontend's four detector branches and the worker must be sound for
the exact current revision; evidence for a previous revision is insufficient.

Narrowing an optimization's accepted inputs leaves declined inputs on the
existing complete route. The new theorem does not claim correctness of that
entire implementation from a Boolean rejection alone; the existing exact-source
supervisor certification and runtime fallback tests remain necessary.

`run-routing-certification-gate.sh` includes the new module, all its axiom audits,
and the frontend projection regressions. `lake env lean` or the module build
alone certifies the stated theorems, not the whole release gate or benchmark.

The updated full routing gate subsequently passed: 77 test executions, the
accepted valid routing fixture, the rejected forged fixture, and all named
axiom audits. The new theorems depend only on `propext`, `Quot.sound`, and where
needed `Classical.choice`; none depends on `sorryAx`. Exact source hashes and
compressed build/gate logs are recorded in
`results/benchmarks/2026-09-17-dynamic-baseline/abox-lean-certification.json`.
This gate result does not substitute for the complete corpus correctness check
or the timed benchmark comparisons.
