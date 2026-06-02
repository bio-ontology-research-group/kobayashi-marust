# kobayashi-marust — engine

The Rust engine of **Kobayashi-MaRust**: an implementation of the **disjunctive
context calculus** of Tena-Cucala,
Cuenca Grau and Horrocks (consequence-based reasoning for `ALCHOIQ` / OWL 2 DL),
the calculus realised in the [Sequoia](https://github.com/andrewdbate/Sequoia)
reasoner.  It is a faithful (single-threaded) port of Sequoia's calculus core:
`context/Rules.scala`, `context/Context.scala`, `context/ContextState.scala`,
and the clause / term / ordering representation in `clauses/package.scala`.

The earlier version of this crate handled only the Horn fragment (disjunctive
heads were deferred), which made it unsound on the interaction of disjunction
with existentials.  This version implements the full disjunctive calculus and is
**sound** (proved in Lean, see `../lean`, and validated against HermiT, see
`../oracle`).

## Calculus

Each named concept `A` seeds a **root context** with core `{A(x)}`; anonymous
successors live in **successor contexts**.  Context clauses `Γ → Δ` (a body
conjunction of predicates implying a head disjunction of literals) are derived by:

| Rule    | Role |
|---------|------|
| Core    | seed `⊤ → A` for each `A` in the context core |
| Hyper   | hyperresolution of an ontology clause's body against maximal context-clause head predicates |
| Pred    | resolve clauses pushed back from a successor against the predecessor's function-term clauses |
| Succ    | push function-term (existential) consequences `C(f(x))`, `R(x,f(x))` to the successor context |
| Eq      | paramodulation with a derived equality (number restrictions / functionality) |
| Ineq    | delete `t ≉ t` from a head (eager) |
| Elim    | redundancy elimination (forward/backward subsumption) |

Terms are integer-encoded exactly as in Sequoia (`x=0`, `y=-1`, `z_i=-(i+1)`,
`f_i(x)=+i`), so the term order is the integer order and function terms are
maximal.  The context literal ordering (`calc::lteq`) is a faithful port of
`ContextLiteralOrdering`.

Expansion strategy: the **trivial** strategy (all successors share one context
with empty core).  This is sound and complete (Simančík et al.) and is the
simplest strategy that preserves the calculus's guarantees; it is not
pay-as-you-go, so it does not yet scale to large classified ontologies.

### Scope (honest)

Implemented and validated: the `ALCHIQ` fragment — concept hierarchy,
disjunction, conjunction, full negation, existentials, universals, role
hierarchy, inverse and symmetric roles, functionality and number restrictions
(via Eq + **Factor**), **nominals** (sound ABox-grounded reduction, see
`py/preprocess.py`), and **transitive roles / role chains** `R∘S⊑T` (reachability
encoding, the role automaton specialised to those shapes, in `py/preprocess.py`).

Still open:

* the **general regular-role-hierarchy automaton** (only transitivity `R∘R⊑R`
  and single chains `R∘S⊑T` are encoded; nested/arbitrary regular hierarchies
  are not);
* the **full Table-3 nominal rules** (Nom / Join / r-Succ / r-Pred), needed only
  for nominal/inverse/number-restriction *merge* interactions beyond the
  ABox-grounded reduction;
* the **pay-as-you-go expansion strategy** (`safeCentral`); the trivial strategy
  is complete but slow on large ontologies.

Dropping a clause only ever costs completeness, never soundness; dropped clauses
are counted.

## Binary: `kobayashi-marust`

Reads `{ "clauses": [<clause>] }` on stdin, writes
`{ "subsumptions": {...}, "derived_clauses": [...], "inconsistent": <bool> }` on
stdout.  A `<clause>` is `{ "body": [<atom>...], "head": [<atom>...] }`; atoms are
`concept` / `role` / `eq`; terms are `var` / `ind` / `aux` / `fun`.  See
`src/json_io.rs`.

* `subsumptions[A]` = entailed superconcepts of named class `A`; contains
  `"owl:Nothing"` iff `A` is unsatisfiable.
* `derived_clauses` = the emitted consequences `A(x) -> B(x)` (and `A(x) ->` for
  clashes), for feeding the grounder.
* `inconsistent` = true iff `owl:Thing` is unsatisfiable.

Set `SROIQ_DEBUG=1` to dump every context and its clauses to stderr.

## Build / test

```sh
cargo build --release          # -> target/release/kobayashi-marust
cargo test --release           # 5 calculus unit tests
```

## Python adapter

```python
from rust_context import rust_context_saturate
subsumptions, derived_clauses = rust_context_saturate(tbox)   # tbox = moose normalise() output
```

## Validation against HermiT

`../oracle/validate.py` compares this engine's subsumptions and consistency
against HermiT (oracle JSON in `../oracle/results`).  Results:

Run `../oracle/validate.py` (it applies `py/preprocess.py` for nominals +
transitivity/chains before saturating).

| ontology       | subsumptions recovered | unsound | spurious unsat |
|----------------|------------------------|---------|----------------|
| disjunction    | 0 / 0 (none exist)     | 0       | 0              |
| kinship_chain  | 0 / 0 (none exist)     | 0       | 0              |
| kinship        | **21 / 21**            | 0       | 0              |
| factor_test (≥3⊓≤2) | unsat detected (= HermiT) | 0 | 0          |
| trans_test (A⊑D via trans) | 1 / 1          | 0       | 0              |
| chain_test (A⊑D via R∘S⊑T)  | 1 / 1          | 0       | 0              |

**Complete** agreement with HermiT on all of the above, with zero unsound
subsumptions and zero spurious unsatisfiable classes.  The full Pizza ontology
saturates soundly (slowly, trivial strategy).
