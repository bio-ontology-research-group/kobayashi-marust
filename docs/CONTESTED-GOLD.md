# Contested gold: where the reference reasoners disagree, and who is right

For the current six-item residual audit and the distinction between exact
closure, verdict adjudication, and absent gold, also see
[`HARD-RESIDUAL-AUDIT.md`](HARD-RESIDUAL-AUDIT.md).

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
`ddmin_entail.py`). They are now committed in-repo at
[`results/contested-cores/`](../results/contested-cores/) (8941, 13912,
15516_norules, 2669_norules) so the proof is self-contained; regenerate from the
witnesses above if ever lost. (10621's core lives on IBEX, job 47787383, not yet
copied.)

## The two harness fixes (so the gold is now correct)

1. `ore_canon.py`: `owl:Thing` in the `owl:Nothing` SCC — and any
   `consistent=false` — now maps to the uniform empty inconsistent signature.
2. `ore_runone.py`: Konclude "All parsers failed" (exit 0, empty output) is now
   flagged `error` and **excluded** from comparison (Konclude provides no valid
   gold for SWRL ontologies).

## Which gold to use (the operating rule)

- Default oracle stays **Konclude**, but only with the `ore_canon` `Thing≡Nothing`
  fix applied.
- **Any SWRL / `DLSafeRule` ontology → use HermiT (on a cleaned core).** Konclude
  cannot parse these, so its recorded gold ("consistent") is a bogus
  parse-failure-exit-0 and is meaningless. The full ORE `DLSafeRule` set is **six**
  ontologies: **2669, 15516, 10860, 10906, 12451, 13129** (found by
  `grep -l DLSafeRule`). HermiT 1.4.6 *also* cannot parse the raw onts (it throws
  `UnsupportedDatatypeException` on `rdfs:Literal`, or "built-in atom not
  supported"), so the authoritative verdict is HermiT on a datatype/SWRL-stripped
  core (a *subset* of the axioms, so a cleaned-core *inconsistent* verdict proves
  the full ontology inconsistent). Verified 2026-06-27:
  | ont | true verdict | evidence |
  |-----|--------------|----------|
  | 2669 | **inconsistent** | HermiT on `results/contested-cores/ore_ont_2669_norules.min.owl` |
  | 15516 | **inconsistent** | HermiT on `ore_ont_15516_norules.min.owl` |
  | 10906 | **inconsistent** | HermiT on the datatype-cleaned ont → `InconsistentOntologyException` |
  | 13129 | consistent | HermiT cleaned → `owl:Thing satisfiable` |
  | 12451 | consistent | HermiT (full parse) → `owl:Thing satisfiable` |
| 10860 | under direct adjudication | HermiT can't parse the raw ontology; no valid Konclude gold exists |

  KM closes 2669/15516/10906 (correctly **inconsistent**) and 13129 (correctly
  consistent) under `KM_HT_RULES=1` (the ABox-seeded HT consistency path,
  commit `ea0d535`); all verdicts match HermiT, zero unsound.
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

## 10621 — historical stale-gold report, current gold corrected

`ore_ont_10621` (FMAInOWL anatomy, ~244k clauses) has **functional boolean
datatype properties**. An older retained report described a Konclude signature
with an empty `#UNSAT` block. That report is stale. The current IBEX signature,
checked on 2026-07-16, contains **33,433 unsatisfiable named classes**, including
`Zone_of_cell`. The ontology genuinely has many unsatisfiable named concepts.
Minimal proof from the told axioms:

```
Zone_of_cell ⊑ Fiat_cell_part ⊑ Fiat_anatomical_structure ⊑ Anatomical_structure
            ⊑ Material_physical_anatomical_entity ⊑ DataHasValue(has_mass, "true"^^xsd:boolean)
Zone_of_cell ⊑ DataHasValue(has_mass, "false"^^xsd:boolean)
FunctionalDataProperty(has_mass)
⟹  Zone_of_cell ⊑ ⊥   (a functional property cannot be both true and false)
```

Three-way adjudication on the minimal extracted ontology (IBEX job 47787383):

| reasoner | `Zone_of_cell` verdict | notes |
|----------|------------------------|-------|
| **HermiT 1.4.6** | `≡ owl:Nothing` (unsatisfiable) | datatype-sound authority — **correct** |
| **KM (CB engine)** | `unsatisfiable: [Zone_of_cell]` | **correct** |
| Current Konclude gold | `Zone_of_cell` unsatisfiable | **correct on the witness** |
| Historical stale gold report | consistent, 0 unsat | wrong/obsolete |
| ELK              | consistent, `Zone_of_cell ⊑ Anatomical_structure` | EL profile drops functional datatypes — **cannot see it** |

So **ELK "consistent" does not adjudicate this ontology** because ELK drops the
functional-datatype consequence. KM's unsatisfiability derivation and the
current Konclude signature agree. The 10621 timeout in KM is
correct-but-expensive classification work, not a gold or soundness defect.

**General rule this establishes:** functional-datatype unsatisfiability is a
Konclude-ORE-gold blind spot. For any datatype-bearing ontology where KM reports
unsat but Konclude + ELK report consistent, re-adjudicate with HermiT before
treating KM as unsound.

## Scope / honesty note

Four ontologies remain proven current Konclude-gold failures (8941, 13912,
15516, 2669 via ddmin cores). The `10621` witness remains proven, but the
current Konclude signature now agrees with it and is no longer a live gold
failure. CLAUDE.md notes HermiT differs
from Konclude on ~12 ontologies overall; the rest are **not yet adjudicated** — do
not assume HermiT is right on those without the same proof. On every proven case so
far, KM agrees with the independently checked witnesses.
