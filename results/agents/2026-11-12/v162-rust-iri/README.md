# v162-rust-iri: IRI identity and no panics in the Rust OWL parser

Branch `v162/rust-iri` from `development/v1.6.2` (17d2ca61). Rust only; no Lean
file changed. Deviation numbers refer to the table in
`results/agents/2026-11-12/v162-parse/README.md`.

## What changed

### Identity by expansion (deviations 1, 2, 3)

KM reads a document through `frontend::builtin_aliases::canonicalize` before
the streaming parser (the orchestrator writes the result as a trusted rewrite,
and `ofn_to_clauses` calls it too). The IRI registry keys entities by spelling,
so the fix makes the canonical text give each IRI exactly one spelling.
`canonicalize_entity_spellings` was rewritten:

- Every abbreviated IRI `p:x` in a logical position (not in annotations, not the
  ontology IRI) is expanded with the document's `Prefix` declarations **and the
  standard prefixes `owl rdf rdfs xsd`**. Literal datatypes (`"1"^^p:dt`) count.
- Vocabulary (expansion in one of the four standard namespaces) takes the
  standard spelling: `x:integer` with `x:` bound to the XSD namespace becomes
  `xsd:integer`, `o:minInclusive` becomes `xsd:minInclusive`, and so on. The six
  OWL semantic constants were already respelled in full by
  `canonicalize_builtins` (unchanged). So builtins, datatypes and facets are
  recognised by their expansion, whatever prefix spells them.
- Any other IRI is respelled as the full IRI `<e>` when the document also
  spells it another way (the full form, or a second prefix). This part existed;
  it now also covers the standard prefixes.
- New: when the document uses the text `p:x` itself as a full IRI `<p:x>` (the
  IRI with scheme `p`), every abbreviated `p:x` is respelled `<ns(p)x>`. Before,
  the registry stripped the brackets and merged the two (deviation 2).
- `iri.rs`: `<owl:Thing>` / `<owl:Nothing>` (full IRIs with scheme `owl`) are no
  longer taken as the builtins; only `owl:Thing`, `owl:Nothing` and the real
  OWL IRIs are.
- Cost: expansion is computed once per distinct spelling (an `FxHashMap` over
  borrowed tokens), the first walk stores no per-occurrence data, and the text
  is rewritten in a second walk only when something must be respelled. A
  document with neither a declared prefix nor `owl:`/`rdf:`/`rdfs:`/`xsd:` in its
  text is not walked. Before, every occurrence of a prefixed name built a
  `String` and was stored.

Display: an entity spelled one way keeps its spelling, so km prints it as
before. An entity spelled several ways is printed as its **full IRI**. In the
`<ex:A>` / `ex:A` case km prints `ex:A` for the full IRI `<ex:A>` and
`http://e.org/#A` for the abbreviated `ex:A`.

`KM_FRONTEND_CHECK` (`orchestrate/frontend_check.rs`) expanded every km name
that starts with a declared prefix. It now leaves alone the names of full IRIs
`<p:x>` of the document (`document_verbatim_names`, a token scan run only when
the text contains `<p:` for a known prefix). Without that, probe 10 would fail
closed although km is right.

### No panics, FSS lexical rules (deviations 4, 5, 7, 8, 9; 6 as a side effect)

- `sexpr.rs`: whitespace is exactly U+20, U+9, U+A, U+D (FSS 2.3). The byte
  table used to add VT, FF, 0x85 and 0xA0; the last two occur inside UTF-8
  characters such as `à` (C3 A0), and the tokenizer sliced inside the
  character and panicked (deviation 5). VT and FF no longer separate tokens
  (deviation 6, changed as a side effect). A comment ends at LF **or CR**
  (deviation 7).
- `parse.rs`: `check_operands` checks the operand counts of every axiom and
  expression against the FSS (and DL-safe SWRL) arities before any observer or
  `add_axiom` sees a node; it runs in `for_each_ontology_child`, the streaming
  walk every frontend pass uses. Axiom annotations are not operands, and a
  literal split by the tokenizer into `"lex"` and `^^dt`/`@lang` counts once.
  It also checks the positions that must hold a single token (individuals,
  data properties, cardinality numbers, the operand of `ObjectInverseOf`).
  `SubClassOf()`, `ObjectIntersectionOf(B)`, `EquivalentClasses(C)` and every
  axiom or constructor with missing operands now give the parser's ordinary
  error (`OutOfFragment("parse error: SubClassOf takes 2 operand(s), found 0")`)
  instead of a panic or a silently different axiom (deviations 8, 9).
- `ObjectInverseOf(ObjectInverseOf(r))` is an **error** (FSS 6.1 allows only a
  named property inside), both in the walker and in `role_cls` (deviation 4).
- Unchecked `args[i]` indexing in `cls` and `add_axiom` became checked operand
  access (`arg`/`op`), so a node built outside the walker cannot panic either.

How a syntax error leaves `km classify`: message on stderr, exit code 2, the
same code as the grammar validator's `invalid OWL 2 DL input` errors. Example
(new binary, probe 14): `parse error: SubClassOf takes 2 operand(s), found 0`,
exit 2. On the base binary the same probe gave the grammar validator's message,
also exit 2; on the new binary the walker answers first because `has_imports`
walks the document before the grammar check.

## Probes through `km classify --lines` (`KM_THREADS=1`)

Raw probes without declarations are rejected by km's declaration check
(exit 2) on both binaries, so `probes/d*.ofn` are declared variants.

| probe | base | new |
|---|---|---|
| `d1-spellings.ofn` (1) | correct (the old mixed-spelling pass already applied) | same output |
| `d10-ambiguous.ofn` (2) | `<ex:A>` and `ex:A` merged: `SUB ex:A ex:B`, `SUB ex:B ex:A` | two entities: `SUB ex:A ex:B`, `SUB ex:A http://e.org/#A`, `SUB ex:B http://e.org/#A` |
| `d2-thing.ofn` (3) | correct (`canonicalize_builtins`) | same |
| `d4-nonascii.ofn` (5) | panic, exit 134 | `SUB ex:à ex:B`, exit 0 |
| `d9-cr.ofn` (7) | `parse error: unexpected end of input`, exit 2 | `SUB http://e#A http://e#B`, exit 0 |
| `4-nonascii-word.ofn` (5) | panic, exit 134 | declaration error, exit 2 |
| `14-empty-subclass.ofn` (8) | grammar error, exit 2 | `parse error: SubClassOf takes 2 operand(s), found 0`, exit 2 |
| `3-double-inverse.ofn` (4) | grammar error, exit 2 | `parse error: operand 1 of ObjectInverseOf must be a name or a literal, found ObjectInverseOf`, exit 2 |

### `KM_FRONTEND_CHECK=1` (`frontend-check-probes.txt`)

Checker: `km-owl-reference` copied from the v1.6.2 worktree (built Nov 12 22:07).

```
=== base d10-ambiguous.ofn
KM_TIMING KM_FRONTEND_CHECK disagreed: SubClassOf(ex:A http://e.org/#A): km=no reference=yes (procedure=el)
KM_FRONTEND_CHECK fail closed: ...; no answer published          (exit 6)
=== new d1-spellings.ofn
KM_TIMING KM_FRONTEND_CHECK agreed procedure=el
=== new d10-ambiguous.ofn
KM_TIMING KM_FRONTEND_CHECK agreed procedure=el
=== new d2-thing.ofn
KM_TIMING KM_FRONTEND_CHECK agreed procedure=el
=== new d4-nonascii.ofn
KM_TIMING KM_FRONTEND_CHECK agreed procedure=el
```

`1-spellings.ofn` itself has no declarations, so km stops at the declaration
check (exit 2) before the frontend check, on both binaries. Its declared
variant `d1-spellings.ofn` agrees (it already agreed on base).

## Tests

Commands (from `engine/`, `CARGO_TARGET_DIR=engine/target CARGO_BUILD_JOBS=2`,
no `KM_HT_*` flags):

```
cargo test --lib frontend
cargo test --lib orchestrate
cargo test --lib                     # whole library, base and new
cargo test --test <t>   for t in builtin_iri_aliases entity_spellings frontend_check
    input_utf8_non_ascii special_source_iris source_axiom_drops
    symbolic_source_classification inverse_role_chains
    universal_role_and_top_data_range has_key_rules
```

| suite | base 17d2ca61 | new |
|---|---|---|
| `--lib` (all) | 3126 passed, 32 failed, 10 ignored | 3139 passed, 30 failed, 10 ignored |
| `--lib frontend` | 467 passed, 1 failed | 477 passed, 2 failed before the fixture fix below; the fixture test passes after it |
| `--lib orchestrate` | 335 passed, 1 failed | 335 passed, 1 failed (same test) |
| 10 integration targets above | 59 passed, 0 failed | 59 passed, 0 failed |

**Newly failing tests: none.** The failure lists of the whole-library runs
differ only in four `elcomplete::tests` that share a process-wide environment
lock and fail as a group depending on order (`rooted environment lock:
PoisonError`): `rooted_batch_reuses_one_fixpoint_but_certifies_each_subject`
failed only in the new run; `multi_role_backlinks_are_input_order_invariant`,
`repair_after_failed_base_check_uses_handed_off_index`,
`repair_passes_on_inert_covering_disjunction` failed only in the base run. All
four pass when run alone on the new branch. The 29 failures common to both runs
are environmental (missing Lean checkers in this worktree's `lean/.lake`,
`KM_HT_*`/rooted-publication requirements), for example
`tableau::hypertableau::tests::native_abox_global_decision_uses_joint_sat_wire`
("native ABox publication requires KM_HT_TOTAL_GLOBAL_ROOTED_ORDINARY_RUN_CHECKER ...").
`frontend::profile::rule_property_kind_tests::graph_source_sorts_survive_frontend_converter_and_worker_wire`
and `orchestrate::frontend_run::tests::positive_el_input_round_trips` fail in
the filtered runs of both base and new and pass in both whole-library runs.

One test changed because it fed invalid syntax:
`frontend::profile::tests::disjoint_union_abox_gate_excludes_component_connectors`
used `HasKey(<A> (<p>))`; FSS 9.5 requires both property lists, so the
fixture is now `HasKey(<A> (<p>) ())` (the new operand check rejected the old
one). Three `builtin_aliases` tests expected alias spellings of non-builtin
OWL-namespace names (`o:NothingElse`, `o:Thing`) to stay untouched; they
are the IRIs `owl:NothingElse` etc., so they now take the standard spelling,
and the tests say so.

New unit tests (module `frontend::parse::deviation_probe_tests`, plus three in
`frontend::sexpr`): `probe_1_two_spellings_are_one_entity`,
`probe_10_full_iri_that_reads_like_an_abbreviation_is_another_entity`,
`probe_2_builtins_by_expansion`, `probe_3_double_inverse_is_an_error`,
`probe_4_non_ascii_bare_word`, `probe_9_cr_ends_a_comment`,
`probe_8_wrong_arities_are_errors`, `probe_14_missing_operands_are_errors`
(every axiom and constructor head with no operands and one short),
`non_ascii_bare_word_is_one_token`, `comments_end_at_cr_or_lf`,
`vertical_tab_and_form_feed_are_not_whitespace`,
`byte_classes_are_the_functional_syntax_whitespace`.

## Output identity (`output-identity.tsv`)

`km classify --lines`, `KM_THREADS=1`, `timeout 300`, at most two runs at a
time, base binary (17d2ca61) and new binary, both release builds:

- the 30 F inputs that use prefixed names (every F input whose text has
  `Class(`/`ObjectProperty(` followed by a non-`<` token; exactly 30, matching
  the v162-parse count),
- 6 more F inputs spread over the size range (21 KB to 23 MB),
- the 6 largest F inputs (575 MB, 394 MB, 394 MB, 350 MB, 305 MB, 275 MB):
  all six ran under 300 s.

**42/42 byte-identical** (`cmp`), all exit 0 on both binaries. Two new-binary
runs of the large inputs (ore_ont_15703, ore_ont_15203) first died while they
ran together: `memory allocation of 4 bytes failed` and `worker engine
terminated by signal 6`, the host commit limit. Rerun alone, both exit 0 and
are identical (first log kept as `ore_ont_15203.owl.err.first-oom` in scratch).

## Parse time (`parse-time-15059.txt`)

Largest input, ore_ont_15059 (576 MB), base and new run one after the other,
alone, `KM_TIMING` line `in-process frontend: parse+clausify+handoff`:

| run | base | new |
|---|---|---|
| with the 42-input batch | 34.89 s | 31.89 s |
| sample 1 | 42.55 s | 34.50 s |
| sample 2 | 48.99 s | 40.21 s |

New is not slower; the host is noisy (load about 25), so read the gain as
"no regression" rather than as a speed-up.

## Open

- Deviations 6 (VT/FF: now not whitespace, changed as a side effect of the
  whitespace fix), 10 (annotation after an operand), 11 (stray IRIs, several
  `Ontology` nodes), 12 (bare non-IRI words, undeclared prefixes in
  `parse_axioms`), 13 (`ObjectInverseOf` in property axioms) are unchanged in
  the parser. In `km classify` the grammar validator and
  `check_iri_prefixes` already reject 10, 11, 12.
- A full IRI whose text reads like a standard abbreviation (`<xsd:integer>`)
  is still read as the XSD datatype by `datatypes::builtin_datatype_key`, which
  strips the brackets. `<owl:Thing>` is fixed in the registry; the datatype
  and facet recognisers were not changed.
- `examples/ofn_dump.rs` still calls `parse::parse_axioms` without
  `canonicalize` (the module is `pub(crate)`), so its `collisions` counter
  reports raw-parser spellings, not what km classifies.
- The incremental scanners `source_locality.rs` and `incr_envelope.rs` still
  end comments only at LF and have their own tokenizers; they were left alone
  (incremental API out of scope).
- `parse_axioms` itself still keys entities by spelling; identity holds for
  every path that canonicalizes first (`km classify`, `ofn_to_clauses*`,
  realization).
