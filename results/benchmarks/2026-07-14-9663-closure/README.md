# ore_ont_9663 closure and 592-ontology regression sweep

Status: complete. This directory records the KM/Konclude comparison, reduced
witnesses, exact constructor ports, promoted production run, and complete IBEX
ORE sweep that close `ore_ont_9663`.

The promoted binary was built on `ws` with Rust 1.85 in the Bullseye container.
Its SHA-256 is
`dbc35ea3f19c5de9ef447ce274edeb69aeacd91867f3e4d51eaf879b6533e825`.
The release suite passes 1,474 tests, with zero failures and 7 ignored tests.

## Production closure

Konclude's official binary completed 9663 in 11.45 seconds and produced the
stored gold signature. The starting KM binary terminated soundly but returned
685,932 of 725,040 non-self pairs, leaving 39,108 missing. The difference was
highly structured: 13,029 subjects each lacked `BFO_0000004` and its two BFO
superclasses, accounting for 39,087 pairs.

| IBEX job | Binary/stage | Result | Missing | Wall | Peak RSS |
|---|---|---|---:|---:|---:|
| 48792307 | official Konclude | exact gold | 0 | 11.45 s | about 4.13 GB |
| 48792370 | KM baseline | incomplete | 39,108 | 12.84 s | about 2.15 GB |
| 48795405 | native source RBox links | incomplete | 633 | 30.42 s | 2,702,468 KB |
| 48795569 | first role-successor closure | exact match | 0 | 1:56.81 | 3,369,420 KB |
| 48797088_0 | promoted provenance build | exact match | 0 | 52.75 s | 3,189,032 KB |
| 48797094_346 | promoted full-sweep task | exact match | 0 | 47 s | 3,147,948 KB |

The final 9663 run has 68,860 base and 68,878 extended saturation items. It
answers 385 unsatisfiable and 57,385 satisfiable subjects by saturation, then
finishes the 422 insufficient subjects through completion with no defer.
Konclude's trace reported 423 insufficient nodes, which confirms the repaired
semantic boundary independently of the final signature comparison.

## Exact Konclude ports

The first missing boundary was source RBox construction. Konclude keeps
property domains and ranges on `CRole`; the source-TBox bridge previously
discarded their clausal copies. The Rust converter now carries exact source
RBox provenance as `(role, concept)` pairs, and source mode installs those pairs
on the role and inverse role before suppressing clausal duplicates.

The remaining 633 pairs required
`CTotallyPrecomputationThread.cpp:2057-2074` and
`CTotallyOntologyPrecomputationItem.cpp:731-739`. When `hasRoleRanges` holds,
Konclude does not reuse the ordinary `(filler, polarity)` item. It constructs a
separate `(role, filler, polarity)` item, stores it in the restriction's
existential-successor reference, includes it in dependency ordering, and
initializes its saturation node with that role. This loads generated role
ranges before the successor is used. KM now performs the same construction.

The reduced causal witness is a domain on `RO_0002202` reached only through
`BFO_0000050 ∘ RO_0002202 ⊑ RO_0002202`. It failed before the role-specific
item port and passes after it. An independent exact port of Konclude's
substitute-chain subsumer extraction remains covered, although its isolated
candidate did not alter 9663.

These changes construct the inputs to the `konclude_ht` saturation engine.
They do not change the CB calculus or its derived clauses, so they need no Lean
re-certification.

## Full-sweep result

IBEX array job 48797094 ran all 592 ORE pool ontologies, one per task, with a
240-second reasoner cap, 20 GB Slurm memory, and the same production
trigger-absorption flags as the preceding 3215 sweep. Every row records the
promoted binary SHA.

| Metric | 3215 baseline | 9663 closure |
|---|---:|---:|
| completed | 574 | 574 |
| timeout | 18 | 18 |
| exact Konclude match | 508 | 511 |
| incomplete | 51 | 48 |
| unsound | 4 | 5 |
| both-disagree | 2 | 1 |
| inconsistent | 6 | 6 |
| no gold | 3 | 3 |

No previously exact ontology regressed. Three incomplete ontologies become
exact: 8730, 11978, and 9663. Ontology 11745 improves from 15,350 extra and
1,213 missing pairs to one extra and zero missing.

The only adverse movement is within the already-open next target, 9724. Its
sound partial signature changes from 3,140 to 3,325 missing pairs, with zero
extras in both. Controlled job 48796214 reproduced the cause: the old binary
constructs 25,964 saturation items, while the exact role-successor port
constructs 33,678 because Konclude's role-automata preprocessing generates
additional ranges. Both runs stop at the fixed 180-second outer-queue cap.
Instrumented Konclude completes 9724 in 9.84 seconds, so this is the remaining
9724 performance gap, not a false inference or a regression of a solved
ontology.

## Reproduction scripts

- `ibex_9663_konclude_baseline.sbatch` and
  `ibex_9663_konclude_trace.sbatch` run the official and instrumented Konclude
  comparisons.
- `ibex_9663_km_baseline.sbatch`, `analyze_9663_diff.py`, and
  `ibex_9663_diff_analysis.sbatch` reproduce the 39,108-pair decomposition.
- `ibex_9663_candidate.sbatch` runs the first exact candidate.
- `ibex_9663_9724_final_gate.sbatch` runs the promoted binary on 9663 and the
  controlled 9724 neighbor.
- `ibex_9663_fullsweep.sbatch` runs the complete 592-ontology IBEX array.
- `compare_sweeps.py` compares that array with the 3215 closure baseline.
- `analyze_ab_delta.py` records exact pair-level changes between two KM JSON
  outputs.

The promoted sweep can be resubmitted on IBEX from the preserved run directory
with:

```bash
sbatch --array=0-591 ibex_9663_fullsweep.sbatch
```

The script defaults to `km-9663-final-bullseye` and records its SHA-256 in
every result row. `KM_SWEEP_BINARY`, `KM_SWEEP_CONFIG`, and the output-directory
variables remain available for a controlled A/B run.

`summary.json` is the machine-readable closure and sweep summary. The full
causal account and C++ source correspondence are in
`docs/SOLVE-7914-9663-9724.md`.
