# Model export: what each route holds (design, 2026-11-16)

Status: not implemented. `km classify --export-model FILE` was requested
(engine round 3, Part 4) so that the proved model checker of the hint route
(`docs/V1.7.0-C5-HINT-ROUTE.md`) can certify negative answers from one
model. This note records what each route holds today and the format the
export should write.

## Proposed format (JSON lines)

One object per line, source-level names (full IRIs), no Lean normal-form
names:

```text
{"kind":"element","id":"e0","classes":["http://x/A", ...],"individuals":["http://x/a"]}
{"kind":"edge","role":"http://x/r","from":"e0","to":"e1"}
{"kind":"same","individuals":["http://x/a","http://x/b"]}
{"kind":"value","element":"e0","property":"http://x/p","literal":"\"1\"^^xsd:integer"}
{"kind":"witness","class":"http://x/C","element":"e3"}
{"kind":"blocked","element":"e7","blocker":"e2"}
```

`blocked` lines mark a finite representation: the model is the
unravelling, and the producer that closes it under the Lean translation
must expand them.

## What each route has

- EL completion (`elc`, `elcomplete.rs`): the saturated sets `S(A)` and the
  role relation `R(r)` over the class names and the existential fillers. That
  is the canonical model directly (one element per named class and per
  filler, edges from `R`), with no blocking; individuals are their nominal
  elements. This is the cheapest exact export and the natural first target.
- Native bridge (`konclude_ht`): one completion graph per probe and one for
  the ABox consistency check (`native_nominal_consistency`). A clash-free
  completed graph of the consistency check is a model of the ontology up to
  blocking (nodes, labels with concept tags mapped back to names through
  `bridged.named`, edges per role tag, merged nodes, blocked nodes). The
  graph is torn down after each probe; exporting needs a hook at the
  consistency fixpoint (where `KM_HT_GRAPH_DUMP` prints it today) and the
  tag-to-name map. Labels hold internal concepts (triggers, definers) that
  must be dropped.
- CB engine (`engine.rs`): saturated contexts, not a model. A model would be
  the standard canonical-model construction of the completeness proof (one
  element per context, edges from successor links), which the Lean side
  formalises but Rust does not build.
- Hypertableau worker (`tableau.rs`): a completed branch with blocking, the
  same shape as the bridge graph.

## Next step

Implement the EL export first (complete and blocking-free), then the
bridge's consistency graph.
