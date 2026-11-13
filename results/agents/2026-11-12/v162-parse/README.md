# v162-parse: executable OFN parser for fragment F, checked against Rust

Branch `v162/parse` (from `development/v1.6.2` at 9feed699). `OWL/Semantics.lean` is unchanged.

## What changed

| file | content |
|---|---|
| `lean/ContextCalculus/OWL/Parse.lean` | `ContextCalculus.OWL.parse : String → Except String Ontology`: byte-level tokeniser, s-expression reader with an explicit stack, converter to the `Semantics.lean` types. The module docstring is the specification of what it accepts, skips and rejects. |
| `lean/ContextCalculus/OWL/Names.lean` | `ClassExpr.roleNames`, `Axiom.classNames`, `Axiom.objectPropertyNames`, `Ontology.classNames`, `Ontology.objectPropertyNames` (deduplicated, first-occurrence order, one pass with a hash set), plus membership and no-duplicate lemmas |
| `lean/ContextCalculus/OWL/ParseTests.lean` | 68 `#guard` unit tests |
| `lean/KMOWLParse.lean`, lakefile target `km-owl-parse` | prints `{"status":"ok","classes":[..],"objectProperties":[..],"axiomCounts":{..}}` (sorted names) or `{"status":"rejected","reason":".."}` |
| `lean/ContextCalculus.lean` | imports the three new modules |
| `engine/examples/ofn_dump.rs` | Rust dump in the same JSON shape (described below). No change to the Rust frontend. |
| `results/.../v162-parse/{classify,differential,summarize}.py` | input classification (survey row x1 = `F`), differential driver, tables |

## Parser rules (summary; the full list is the docstring of `Parse.lean`)

- Whitespace: U+20, U+9, U+A, U+D (FSS 2.3). Comment: `#` where a token may start, up to LF or CR. Full IRI: `<` up to the next `>`, verbatim. String literal: `"` up to the next unescaped `"`, where a backslash escapes the next byte. Typed and language-tagged literals split into a literal and a word, as in Rust. Unterminated IRIs and literals are syntax errors.
- A word made only of ASCII letters and followed by `(` opens a list (`sexpr.rs` rule).
- Prefixes: `owl rdf rdfs xsd` are predeclared with the FSS Table 2 namespaces, the same four as `conformance.rs` (`xml:` is predeclared by neither the standard nor Rust). Redeclaring a standard prefix with its own namespace is allowed. Rebinding it to another namespace, declaring a prefix twice, or using an undeclared prefix is an error. `p:local` splits at the first `:` and expands to `ns ++ local`. `<iri>` stays verbatim. The empty prefix works (`Prefix(:=<..>)`, `:A`).
- `owl:Thing` / `owl:Nothing` are recognised after expansion (any spelling) and become `.thing` / `.nothing`. Declarations of them are skipped. `ObjectInverseOf(ObjectInverseOf(r))` is `r`.
- Document: `Prefix(..)*` followed by one `Ontology(` [IRI [version IRI]] `Import*` `Annotation*` axioms `)`, then the end of the text. Leading axiom annotations are skipped.
- Accepted: SubClassOf, EquivalentClasses, DisjointClasses, ObjectPropertyDomain, ObjectPropertyRange, SubObjectPropertyOf (an atomic property or an ObjectPropertyChain of at least 2), EquivalentObjectProperties, InverseObjectProperties, Transitive- and SymmetricObjectProperty, Declaration(Class) and Declaration(ObjectProperty). Class expressions: names, Thing, Nothing, Intersection, Union, Complement, Some, All. Object-property expressions: names and ObjectInverseOf, accepted in every property position, including the RBox axioms. Operand counts follow FSS: EquivalentClasses, DisjointClasses, EquivalentObjectProperties, ObjectIntersectionOf and ObjectUnionOf need at least 2.
- Skipped: Annotation, AnnotationAssertion, SubAnnotationPropertyOf, AnnotationPropertyDomain and AnnotationPropertyRange, and declarations of annotation properties, data properties, named individuals and datatypes.
- Rejected with `out of fragment: <construct> (<class>)`: imports, ABox assertions, data constructs and data-property axioms, cardinalities, nominals (ObjectOneOf, ObjectHasValue), ObjectHasSelf, DLSafeRule, HasKey, DisjointUnion, functional, inverse-functional, reflexive, irreflexive and asymmetric properties, DisjointObjectProperties, `owl:topObjectProperty`, `owl:bottomObjectProperty`, anonymous individuals. Syntax errors give `syntax error: ...`. Every rejection is an `Except.error`. The functions are total (structural fuel or `termination_by`), with no `partial` and no panics.
- Cost: tail-recursive loops over the bytes. The converter recurses only on the nesting depth inside one axiom. Repeated spellings are resolved once through a memo table, and repeats share one string.

## Theorems (Names.lean)

```lean
theorem Ontology.mem_classNames (O : Ontology) (a : IRI) :
    a ∈ O.classNames ↔ ∃ ax ∈ O.axioms, a ∈ ax.classNames
theorem Ontology.classNames_nodup (O : Ontology) : O.classNames.Nodup
theorem Ontology.mem_objectPropertyNames (O : Ontology) (r : IRI) :
    r ∈ O.objectPropertyNames ↔ ∃ ax ∈ O.axioms, r ∈ ax.objectPropertyNames
theorem Ontology.objectPropertyNames_nodup (O : Ontology) : O.objectPropertyNames.Nodup
```

```
'ContextCalculus.OWL.Ontology.mem_classNames' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWL.Ontology.classNames_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWL.Ontology.mem_objectPropertyNames' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWL.Ontology.objectPropertyNames_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The new files contain no `sorry`, `native_decide`, `partial`, axioms, or raised limits.

## Build and test

```
cd lean && LEAN_NUM_THREADS=2 nice lake build ContextCalculus km-owl-parse   # 8686 jobs, success
cd engine && CARGO_TARGET_DIR=$PWD/target CARGO_BUILD_JOBS=2 CARGO_PROFILE_RELEASE_LTO=false \
  CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 CARGO_PROFILE_RELEASE_PANIC=unwind \
  cargo build --offline --release --example ofn_dump                         # success
python3 classify.py inputs.tsv
python3 differential.py inputs.tsv OUT km-owl-parse ofn_dump [--only-f]      # 2 in flight, nice, timeout 300
python3 summarize.py OUT/results.jsonl > summary.md
```

All 68 `#guard`s pass (they run during the build of `ParseTests`). The release-profile overrides only make the example build faster and let it catch panics. The KM release build is unaffected.

## The Rust dump (`engine/examples/ofn_dump.rs`)

- Names come from the Rust parse itself: `parse::parse_axioms` builds the Rust `Ontology`, `rbox::rbox_node` supplies the records (atomic domains and ranges exist only there), and `Declaration(Class|ObjectProperty)` nodes add the declared names. Each name is mapped back with `IriRegistry::full_iri`, and generated names (`__inv__r`, `__dt__…`) are dropped with `is_named_iri`.
- The Rust registry keys entities by their raw spelling and never expands a prefix. So the dump expands each raw spelling with the document's `Prefix` declarations and the four standard prefixes. It also reports `collisions` (distinct Rust entities that expand to one IRI) and `ambiguous` (one Rust entity reached by both a full and a prefixed spelling).
- `axiomCounts` counts the `Ontology(..)` children per head, as the Rust tokeniser and s-expression parser deliver them. The dump also reports `conformance::check_iri_prefixes` and the parser's dropped-axiom counts.

## Differential results (1,781 survey inputs; data in `results.jsonl`, tables in `summary.md`)

| | inputs |
|---|---:|
| F inputs (survey row x1) | 499 |
| Lean accepts | 499 |
| Lean and Rust agree (class set, object-property set, all 12 axiom counts) | 499 |
| disagree | 0 |
| Rust rejects or crashes | 0 |
| Rust registry flags (collisions, ambiguous, undeclared prefix, failed prefix check, dropped axioms) | none |

Of the F inputs, 469 spell entities only as full IRIs and 30 only as prefixed names. No F input mixes the two. So prefix expansion is exercised on 30 inputs, and prefix identity is never tested by the suite (plan, section 3).

Non-F inputs (1,282): Lean rejects 1,281 without a crash. Rejections by reason (the first construct outside F in document order):

| reason | inputs |
|---|---:|
| ClassAssertion (ABox assertion) | 261 |
| ObjectMaxCardinality (cardinality restriction) | 175 |
| FunctionalObjectProperty (object property characteristic) | 134 |
| ObjectMinCardinality (cardinality restriction) | 122 |
| ObjectOneOf (nominal) | 112 |
| ObjectPropertyAssertion (ABox assertion) | 71 |
| ObjectHasValue (nominal) | 69 |
| ObjectExactCardinality (cardinality restriction) | 54 |
| DataHasValue (data construct) | 43 |
| DataPropertyDomain (data property axiom) | 42 |
| DataMinCardinality (data construct) | 33 |
| owl:topObjectProperty | 25 |
| DataSomeValuesFrom (data construct) | 21 |
| DataMaxCardinality (data construct) | 20 |
| FunctionalDataProperty (data property axiom) | 18 |
| DataPropertyAssertion (ABox assertion) | 13 |
| DataExactCardinality (data construct) | 11 |
| DataPropertyRange (data property axiom) | 11 |
| ReflexiveObjectProperty (object property characteristic) | 10 |
| DataAllValuesFrom (data construct) | 10 |
| SameIndividual (ABox assertion) | 7 |
| InverseFunctionalObjectProperty (object property characteristic) | 7 |
| ObjectHasSelf (self restriction) | 4 |
| DisjointUnion (disjoint union) | 3 |
| SubDataPropertyOf (data property axiom) | 3 |
| DLSafeRule (rule) | 1 |
| syntax error: unexpected @prefix before Ontology (the Turtle fixture) | 1 |

Lean accepts one non-F input: `v150-corpus/files/ore_ont_7216.owl`. The input is in F, so the survey is wrong. Its head counter reads `Gt(` inside the IRI `<...#Gt(ROSA)26Sortm2(SNCA*119)Djmo>` as a construct. Lean and Rust agree on it (631 classes, 7 properties, same counts). So F has 500 suite inputs, not 499. The same counter produced the `Hz` head in the survey, probably for the same reason.

## Parse times of the five largest F inputs (ws, one process, `nice`)

| input | MB | axioms | Lean wall s | Lean read / parse | Lean max RSS MB | Rust dump wall s |
|---|---:|---:|---:|---|---:|---:|
| ore_ont_15059.owl | 577 | 3,280,784 | 20.2 | 3.0 s / 13.0 s | 2,198 | 27.6 |
| ore_ont_1559.owl | 394 | 2,513,931 | 17.3 | 2.4 s / 9.8 s | 1,550 | 14.2 |
| ore_ont_15203.owl | 394 | 2,513,922 | 17.5 | 2.5 s / 9.9 s | 1,552 | 19.0 |
| ore_ont_3836.owl | 350 | 1,928,386 | 10.7 | 2.0 s / 7.1 s | 1,340 | 8.0 |
| ore_ont_3524.owl | 305 | 2,097,631 | 9.4 | 2.2 s / 5.8 s | 1,159 | 6.7 |

Wall time includes the name lists, sorting and JSON output. Lean's total over all 499 F inputs is 276 s. The first run timed out (300 s) on four NCBITaxon inputs (178 MB, 981,151 classes). Parsing them took 6 s. The time went to `Array.qsort` on the nearly sorted name list in the executable's output code, not in the parser. `km-owl-parse` now sorts with `List.mergeSort`, and ore_ont_868 takes 6.5 s.

## Rust deviations from the OWL 2 functional syntax specification

Each deviation was reproduced with `ofn_dump` on an input in `deviation-probes/`. Every deviation was left unchanged in Rust. None occurs on a suite input: 499/499 F inputs agree, and the registry flags are clean.

| # | probe | Rust behaviour | spec |
|---|---|---|---|
| 1 | `1-spellings.ofn` | `ex:A` and `<http://e.org/#A>` are two entities (registry keyed by raw spelling, no prefix expansion) | FSS 2.4 / 3.7 (abbreviated IRIs denote their expansion) |
| 2 | `10-ambiguous.ofn` | the full IRI `<ex:A>` and the prefixed `ex:A` are merged into one entity | FSS 2.4 |
| 3 | `2-thing.ofn` | `o:Thing` with `o:` bound to the OWL namespace is an ordinary class (only `owl:Thing` and the full IRI are builtins) | FSS 2.4, 5.1 |
| 4 | `3-double-inverse.ofn` | `ObjectInverseOf(ObjectInverseOf(r))` becomes the inverse of a property named `""` (`role_cls` takes `as_atom().unwrap_or("")`) | FSS 6.1 allows only a named property inside ObjectInverseOf. Rust neither rejects it nor reads it as `r` |
| 5 | `4-nonascii-word.ofn` | panics (`byte index is not a char boundary`) on a bare word containing `à`, because bytes 0x85 and 0xA0 count as whitespace | FSS 2.3 (whitespace is U+20, U+9, U+A, U+D) |
| 6 | `13-vt.ofn` | VT and FF separate tokens | FSS 2.3 |
| 7 | `9-cr-comment.ofn` | a comment ends only at LF, so a CR-terminated comment swallows the rest of the document | FSS 2.3 |
| 8 | `14-empty-subclass.ofn` | `SubClassOf()` panics (index out of bounds, `parse.rs:389`). Missing operands panic in most `add_axiom` arms | FSS 9 (axiom arities) |
| 9 | `8-arity.ofn` | `ObjectIntersectionOf(B)` and `EquivalentClasses(C)` are accepted; the latter produces no axiom, so `C` is not even a name | FSS 8.1, 9.1 (at least two operands) |
| 10 | `6-annotation-after.ofn` | `Annotation(..)` is accepted after an operand | FSS 9 (axiom annotations come first) |
| 11 | `7-stray-iri.ofn`, `15-two-ontologies.ofn` | stray IRIs in `Ontology(..)`, several `Ontology(..)` nodes and arbitrary top-level lists are accepted | FSS 3.7 |
| 12 | `11-bare-names.ofn`, `12-undeclared-prefix.ofn` | words that are not IRIs (`A`) and undeclared prefixes are accepted by `parse_axioms`. `conformance::check_iri_prefixes` flags the second at the user-source boundary | FSS 2.4, 3.7 |
| 13 | `5-inverse-subrole.ofn` | `ObjectInverseOf` in SubObjectPropertyOf, EquivalentObjectProperties, InverseObjectProperties, Transitive and Symmetric is rejected (`named role expected`). The Rust frontend does not cover this part of F. Lean accepts it. Zero suite inputs use it | not a misreading. Rust does not cover this part of F |

## Open

- No theorem about `parse` itself (for example, that a printed ontology parses back). The differential test and the unit tests are the evidence.
- `ObjectInverseOf(ObjectInverseOf(r))` is accepted as the brief asks, although FSS 6.1 rejects it as syntax.
- The survey's head counter should skip IRIs (ore_ont_7216). This branch does not change `aggregate.py`.
