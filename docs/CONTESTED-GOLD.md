# Contested gold: where the reference reasoners disagree, and who is right

This is the durable record of the ORE-2015 ontologies where the recorded gold
(Konclude) was **wrong** and KM was right. It exists so we never benchmark
against the wrong oracle. Short answer:

> On every contested ontology proven so far, the correct verdict is
> **inconsistent**, which is **HermiT's** verdict. Konclude's recorded "gold"
> was wrong for two distinct, benchmark-harness / parser reasons (not a KM bug
> and, on two of them, not even a Konclude *reasoning* error).

## The four proven cases

Proof method: delta-debug (`ddmin` over the axioms, oracle = HermiT reports
inconsistent) reduced each ontology to a 2–8 axiom **inconsistent core**, then
ran that core through **both HermiT and Konclude directly**.

| ont   | proven truth | HermiT | Konclude (reasoning) | recorded gold (raw) | root cause of the wrong gold |
|-------|--------------|--------|----------------------|---------------------|------------------------------|
| 8941  | inconsistent | inconsistent ✓ | inconsistent ✓ (prints `EquivalentClasses(Thing Nothing …)`) | "consistent" ✗ | `ore_canon.py` mis-canonicalised Konclude's `Thing≡Nothing` (its encoding of inconsistency) as "consistent + N unsat classes" |
| 13912 | inconsistent | inconsistent ✓ | inconsistent ✓ (same `Thing≡Nothing`) | "consistent" ✗ | same `ore_canon.py` bug |
| 15516 | inconsistent | inconsistent ✓ | **cannot parse** (SWRL `DLSafeRule`; exits 0 with empty output) | "consistent" ✗ | `ore_runone.py` recorded Konclude's parse-failure-exit-0 as a bogus "consistent" |
| 2669  | inconsistent | inconsistent ✓ | **cannot parse** (SWRL `DLSafeRule`) | "consistent" ✗ | same `ore_runone.py` bug |

Minimal inconsistent cores (witnesses):
- **8941**: `DataPropertyRange(hasTopic xsd:string)` + a language-tagged literal
  `"Tarifvertrag"@de` (an `rdf:PlainLiteral`, never in the `xsd:string` value
  space) ⇒ inconsistent.
- **13912**: symmetric `Owner` + `domain(Owner)=Photo` + `Photo ⊑ =1 Owner`
  merges two photos, then `Photo ⊑ ≤1 url` clashes their distinct urls.
- **15516 / 2669**: `DisjointClasses(DBKeyAttribute, DBNonKeyAttribute)` +
  `DBNonPrimaryKeyAttribute ≡ union(...) ⊑ DBKeyAttribute` +
  `ClassAssertion(DBNonKeyAttribute, salary)` ⇒ inconsistent.

The minimal `.min.owl` cores were produced on `ws:~/minimize/` (via
`ddmin_entail.py`). ws is intermittently down; regenerate from these witnesses
if the files are lost. **TODO: copy the four `.min.owl` cores into
`results/contested-cores/` so the proof is self-contained in the repo.**

## The two harness fixes (so the gold is now correct)

1. `ore_canon.py`: `owl:Thing` in the `owl:Nothing` SCC — and any
   `consistent=false` — now maps to the uniform empty inconsistent signature.
2. `ore_runone.py`: Konclude "All parsers failed" (exit 0, empty output) is now
   flagged `error` and **excluded** from comparison (Konclude provides no valid
   gold for SWRL ontologies).

## Which gold to use (the operating rule)

- Default oracle stays **Konclude**, but only with the `ore_canon` `Thing≡Nothing`
  fix applied.
- **Any SWRL / `DLSafeRule` ontology → use HermiT.** Konclude cannot parse these;
  its output is meaningless. (15516, 2669 are the known ORE members; any future
  DLSafeRule ontology is in the same class.)
- Whenever HermiT says *inconsistent* and the recorded Konclude gold says
  *consistent* via a `Thing≡Nothing` encoding or an empty/parse-failure output,
  **HermiT is correct.**

## Host caveat (gold copies can be stale)

Each benchmark host carries its own copy of the gold signatures; they were not
all regenerated together. Verified 2026-06-17 on IBEX
(`/ibex/scratch/hohndor/km/gold/`):

| ont   | IBEX gold first line | correct? |
|-------|----------------------|----------|
| 8941  | `0` (inconsistent)   | ✓ corrected |
| 13912 | `0` (inconsistent)   | ✓ corrected |
| 15516 | `1` (consistent)     | ✗ **stale** — should be excluded (SWRL, Konclude can't parse) |
| 2669  | `1` (consistent)     | ✗ **stale** — should be excluded |

Action on IBEX: exclude 15516 / 2669 from Konclude comparison (or drop their
gold files), since Konclude cannot produce a valid signature for them.

## Scope / honesty note

Only these **four** ontologies have been *proven* (ddmin core + both reasoners).
CLAUDE.md notes HermiT differs from Konclude on ~12 ontologies overall; the other
~8 are **not yet adjudicated** — do not assume HermiT is right on those without
the same ddmin-core proof.
