# v1.6.0 Common-Source EL Recogniser (`ELCommonSourceRecognizer`)

## Summary

This note documents the implementation and verification of the pure-EL common-source recogniser in `lean/ContextCalculus/ELCommonSourceRecognizer.lean` and its unit test suite in `lean/ContextCalculus/ELCommonSourceRecognizerTests.lean`.

1. **Executable recogniser (`recognizeEL`)**:
   - Parses `source : List FCL` into an intermediate representation (`List ParsedItem`) via a proof-producing single-clause classifier (`classifyClauseWithProof`), failing closed (`none`) on any clause outside the accepted table.
   - Selects distinguished `top` and `bottom` concepts from `source` when a total concept clause `⟨[], [C a x]⟩` or an `nf5` clause `⟨[C a x], []⟩` is present, and otherwise allocates fresh identifiers (`freshBase` and `freshBase + 1`) strictly above every concept in `named` and `source`.
   - Pairs existential introduction halves `⟨[C a x], [R r x (app f x)]⟩` and `⟨[C a y], [C b (app f y)]⟩` across the clause list by function symbol `f` and subject `a` in either clause order, rejecting unpaired halves and duplicate function symbols.
2. **Semantic equivalence theorems (`recognizeEL_entails_iff`, `recognizeEL_unsat_iff`)**:
   - Proved without `sorry` or `native_decide`.
   - Both theorems depend only on `[propext, Classical.choice, Quot.sound]`.
3. **Unit tests (`ELCommonSourceRecognizerTests.lean`)**:
   - Registered in `lean/ContextCalculus.lean`.
   - Checks each accepted clause shape alone, `nf3` pairs in both orders, explicit total concepts, fresh `top`/`bottom` allocation when no total concept clause is present, and fail-closed rejections (equality literal, unpaired `nf3` role/filler halves, function symbol used twice, and individual constant) via `by decide` / `by rfl` and `#eval`.

## Clause-Shape Audit Across Frontend, CB Wire, and ELC Wire

We audited `engine/src/frontend/` (`normalise.rs`, `preprocess.rs`), `engine/src/cb_source.rs`, `engine/src/clause.rs`, `engine/src/reasoner.rs`, `engine/src/elcomplete.rs`, `lean/ContextCalculus/CBSourceWire.lean`, `lean/ContextCalculus/ELCommonSourceWire.lean`, and `lean/ContextCalculus/ELRawNormalization.lean`:

| Feature | Frontend / ELC Wire | CB Source Wire | Recogniser Handling |
|---|---|---|---|
| `nf4` body literal order | `normalise.rs` and `ELNormalCheckerTermEmbedding` emit role-first `[R r x y, C b y] -> [C c x]` | `OntologyClause::new` (`clause.rs`) sorts `Pred::Concept` before `Pred::Role`, producing `[C b y, R r x y] -> [C c x]` | Accepts both `[R r x y, C b y]` and `[C b y, R r x y]` with `x ≠ y` |
| `nf7` body literal order | `normalise.rs` emits `[R r y x, R s x z1] -> [R t y z1]` | `OntologyClause::new` sorts the two body role atoms by `(role_id, s, t)` | Accepts both `[R r x y, R s y z]` and `[R s y z, R r x y]` with distinct `x, y, z` |
| Variable numbering | `ELNormalCheckerTermEmbedding` uses `0, 1, 2`; `ELRawNormalization` uses `Nat` variable IDs | `cb_source.rs` maps `"x"` to `0`, `"y"` to `-1`, `"z1"` to `-2`; `normalise.rs` centers binary role chains on `"x"` (`0`) from `"y"` (`-1`) to `"z1"` (`-2`) | Accepts any per-clause injective `Int` variable assignment |
| Role domain (`ObjectPropertyDomain`) | `preprocess.rs::domain_range_clauses` emits `[R r x y] -> [C c x]`; `elcomplete.rs` (`is_pure_el_shape`, `to_nf`) and `ELRawNormalization` (`existsTop`) map this to `nf4 r top c` | Same clause `[R r 0 (-1)] -> [C c 0]` | Extended table and proof to accept `⟨[R r x y], [C c x]⟩` (`x ≠ y`) as `nf4 r top c` |
| Binary disjointness (`A ⊓ B ⊑ ⊥`) | `normalise.rs` (under `trigger_absorb`), `elcomplete.rs`, and `ELRawNormalization` (`bottom`) map `[C a x, C b x] -> []` to `nf2 a b bottom` | Same clause `[C a 0, C b 0] -> []` | Extended table and proof to accept `⟨[C a x, C b x], []⟩` as `nf2 a b bottom` |
| `nf3` Skolem halves | `normalise.rs` emits role half then filler half; `ELNormalCheckerTermEmbedding` uses `2 * s`; `CBEqEncoding` uses `Nat.pair idx 0`; `cb_source.rs` uses `1, 2, ...` | Role half and filler half may appear in either order | Pairs role and filler halves by `(f, a)` in either order; rejects orphans and reused `f` |

## Verification

Command run in `lean/`:

```bash
export PATH=$HOME/.elan/bin:$PATH
cd lean && LEAN_NUM_THREADS=2 nice lake build \
  ContextCalculus.ELCommonSourceRecognizer \
  ContextCalculus.ELCommonSourceRecognizerTests \
  ContextCalculus.KMConcreteWorkerAdapters
```

Axiom audit output from `ContextCalculus.ELCommonSourceRecognizer`:

```text
'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```
