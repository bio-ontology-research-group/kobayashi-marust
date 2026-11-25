# v170-c0-parse: the OWL 2 DL parser of stage C0, checked against Rust

Branch `v170/owl-model`. The Lean parser (`OWL/Parse.lean`, executable
`km-owl-parse`) now reads the OWL 2 DL model of `OWL/Semantics.lean`. This
directory holds the comparison with the Rust parser on survey inputs outside
the v1.6.2 fragment F, as asked in the C0 brief, item 9.

## Tools

| file | content |
|---|---|
| `differential.py` | runs `km-owl-parse` and the v1.6.2 Rust dump (`ofn_dump`, binary `/mnt/data1/leechuck/km-work/v162/scratch/parse/bin/ofn_dump`; source `engine/examples/ofn_dump.rs`, unchanged) per input, two in flight, `nice`, `timeout 300` |
| `heads.py` | independent axiom-head count of an OFN file (a Python s-expression reader), keyed like the Lean `axiomCounts` |
| `heads_check.py` | reruns `heads.py` on every accepted input and compares with the stored Lean counts |
| `summarize.py` | tables; reruns both dumps on inputs with an object-property disagreement to classify it |
| `regress_f.py` | v1.6.3 `km-owl-parse` against the C0 one on the 499 fragment-F inputs |
| `inputs-v162.tsv` | the v1.6.2 survey input list (copied from `../../2026-11-12/v162-parse/`) |

What is compared, per input: accept/reject; the class and object-property
name sets (Lean against Rust); the 12 axiom counts that the Rust dump
reports; every Lean axiom count (38 kinds) against `heads.py`. The Rust dump
has no counts for the new axiom kinds, which is why `heads.py` exists.

## Results

| run | inputs | both accept | Lean rejects, Rust accepts | disagreements after classification |
|---|---:|---:|---:|---:|
| ORE inputs outside F, at most 60 MB (`results.jsonl`, `summary.md`) | 609 | 603 | 6 (all `DLSafeRule`) | 0 |
| other survey inputs outside F (`results-nonore.jsonl`, `summary-nonore.md`) | 653 | 539 | 114 (all `DLSafeRule`) | 0 |
| fragment-F inputs, v1.6.3 against C0 `km-owl-parse` (`regress-f.jsonl`) | 499 | 499 | 0 | 0 |

- Accept/reject: the Lean parser rejects only `DLSafeRule` documents (the
  brief keeps rules rejected). No ill-typed literal or bad facet occurs in
  these inputs. Rust accepts every input.
- Class names: identical on every input both accept.
- The 12 shared axiom counts: identical on every input both accept.
- All 38 Lean axiom counts: identical to `heads.py` on every accepted input
  (see `heads-check.txt` for the full rerun).
- Object-property names differ on 252 ORE and 232 other inputs. In every
  case no name is Lean-only, and every Rust-only name is either a Lean data
  property (the Rust dump lists data properties among its object properties)
  or `owl:topObjectProperty` / `owl:bottomObjectProperty` /
  `owl:topDataProperty` / `owl:bottomDataProperty`, which the Lean model
  represents as `ObjProp.top` / `.bot` and `DataProp.top` / `.bot`, not as
  IRIs.
- Fragment F: the C0 parser gives the same status, class and object-property
  names and the 12 old axiom counts as the v1.6.3 parser on all 499 inputs.

Not exercised by these inputs: `HasKey`, the two negative assertions,
`DatatypeDefinition` and `DisjointDataProperties` occur in no accepted input
of either run (see the kind tables in the two summaries).
`ParseTests.lean` covers each of them.
