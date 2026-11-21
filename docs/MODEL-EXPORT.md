# Model export (`km classify --export-model FILE [--export-model-budget SECONDS]`)

Status: implemented on the `el-canonical`, `ht-bridge`, and `cb-horn` routes.

`km classify --export-model FILE` writes a finite representation of a model of
the input ontology over source-level IRIs after classification finishes. The
answering run captures its terminal completion or saturation state in place so
the export reads that state directly without re-parsing or re-classifying the
ontology from scratch. When `--export-model` is omitted, no export state is
retained and classification pays zero overhead.

`--export-model-budget SECONDS` bounds post-classification model verification
and residual witness probes (default: `1x classify_time + 2 s`). When the budget
expires before all per-class witness probes finish on `ht-bridge`, the exporter
writes the consistency model and every class witness established so far with
`"status": "partial"` and `"reason"` in the header line.

## JSON lines format (`km-model-v1`)

Each line is a JSON object with a `"kind"` field. All class, role, data
property, and individual names are expanded to full source IRIs (internal
normalizer symbols such as `Q_*`, `__def__*`, and `__trig__*` are stripped).

1. **Header (`"kind": "model"`)**
   - Consistent ontology:
     ```json
     {"kind":"model","format":"km-model-v1","status":"ok","route":"el-canonical","elements":3,"edges":1,"closure":"none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)","witness_exact":true,"blocked":0}
     ```
   - Partial export (consistency model and witnesses found within `--export-model-budget`):
     ```json
     {"kind":"model","format":"km-model-v1","status":"partial","reason":"export budget (2.50s) exceeded after 412 of 1200 residual class witness probe(s)","route":"ht-bridge","elements":845,"edges":1920,"closure":"none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)","witness_exact":false,"blocked":0}
     ```
   - Inconsistent ontology:
     ```json
     {"kind":"model","format":"km-model-v1","status":"inconsistent"}
     ```
   - Declined input (outside the implemented model-export fragment):
     ```json
     {"kind":"model","format":"km-model-v1","status":"declined","reason":"cb-horn unit-fact structure does not satisfy non-Horn clause"}
     ```

2. **Domain elements (`"kind": "element"`)**
   ```json
   {"kind":"element","id":"e0","context":"⊤","classes":[]}
   {"kind":"element","id":"e1","context":"http://example.org/A","classes":["http://example.org/A","http://example.org/B"],"individuals":["http://example.org/a","_:genid2147483648"]}
   ```
   `classes` lists the source classes that hold at `id`. `individuals` (omitted
   when empty) lists the named and anonymous individuals interpreted by `id`.
   Named individuals use their full source IRI; anonymous individuals
   (`AnonymousIndividual(_:label)` in OWL 2 Functional-Style Syntax) retain
   their source blank-node identifier `_:label` (for example,
   `_:genid2147483648`), which downstream hint converters map to
   `urn:km:owl-anon:#label`.

3. **Object-property edges (`"kind": "edge"`)**
   ```json
   {"kind":"edge","role":"http://example.org/r","from":"e1","to":"e2"}
   ```
   Edges are closed under the RBox (sub-roles, inverse roles, symmetric roles,
   reflexive roles, transitive roles, and role chains). If RBox closure would
   exceed 250,000 edges, model export declines (`"status": "declined"`) rather
   than emitting a truncated edge set.

4. **Data-property values (`"kind": "value"`)**
   ```json
   {"kind":"value","element":"e1","property":"http://example.org/p","cell":"__dt__val__\"1\"^^xsd:integer","datatypes":["__dt__integer","__dt__val__\"1\"^^xsd:integer"],"literal":"\"1\"^^xsd:integer"}
   ```

5. **Merged individuals (`"kind": "same"`)**
   ```json
   {"kind":"same","individuals":["http://example.org/a","http://example.org/b"],"element":"e1"}
   ```
   Emitted whenever two or more individuals denote the same domain element
   (using full IRIs for named individuals and `_:label` for anonymous
   individuals).

6. **Blocked tableau nodes (`"kind": "blocked"`)**
   ```json
   {"kind":"blocked","element":"e4","blocker":"e2"}
   ```
   Marks a finite cycle in a tableau completion graph: in the unravelled model,
   `element` inherits the outgoing role successors of `blocker`.

7. **Satisfiable class witnesses (`"kind": "witness"`)**
   ```json
   {"kind":"witness","class":"http://example.org/A","element":"e1","exact":true}
   ```
   Maps each satisfiable named class `C` to one or more elements `e` in whose
   `classes` list `C` appears. When `"exact": true`, the source classes of `e`
   equal the entailed named superclasses of `C` (`{D | O |= C <= D}`). When
   `"exact": false` (for example, when `C <= D1 or D2` is a covering union that
   entails neither disjunct alone), no single element in any model can avoid
   every non-entailed disjunct; the exporter then emits covering `"kind":
   "witness"` lines for `C` (one per disjunct branch `e_1, ..., e_k` with
   `"exact": false`) so that the intersection of `classes(e_i)` over the
   witnesses of `C` equals `{D | O |= C <= D}`.

8. **Unseparated nominal rows and auxiliary base model (`"unseparated_rows"`, `"aux_*"`)**
   When a class witness probe on `ht-bridge` merges into shared nominal nodes
   (`rep_id < 0`), a non-entailed class `D` forced onto a nominal `o` by another
   class probe `C` can pollute `o` in the merged model `M_0`, leaving a negative
   subsumption `E not<= D` (where `E <= {o_1, ..., o_k}`) unseparated in `M_0`.
   Whenever the exporter detects such a pair `(E, D)` whose witnesses in `M_0`
   all contain `D` even though `(E, D)` is not an entailed subsumption, it:
   - lists those pairs in `"unseparated_rows": [["http://.../E", "http://.../D"], ...]`
     on the `"kind": "model"` header line, and
   - emits the unpolluted consistency-base model (`raw.base_labels` and
     `raw.base_edges`, where the non-entailed class probes `C` are empty) as
     `"kind": "aux_element"`, `"kind": "aux_edge"`, `"kind": "aux_same"`, and
     `"kind": "aux_witness"` lines whenever the base model separates any row in
     `"unseparated_rows"`.
   Downstream hint generation (`km-hints from-export`) emits the primary model as
   `model0` and the auxiliary base model as `model1` so every negative row is
   confirmed by at least one exported model.

---

## Using the exported model for ABox queries (`--values`, `--same`, `--different`)

When `km classify` runs with `--values`, `--same`, or `--different`,
`ModelAboxPlan::from_exported_model` (`engine/src/orchestrate/abox_rows.rs`)
uses the captured `ExportedModel` together with a dual lower/upper bound test so
that non-canonical model choices never fabricate positive answers or suppress
entailed inequalities:

1. **`SAME` and `TYPE` on `ht-bridge`**:
   - When the retained consistency completion (`harvested_base_comp`) finishes
     with zero nondeterministic choice points (`used_choice_points == 0`), every
     individual node label and node merge in `harvested_base_comp` was derived by
     deterministic hypertableau unit/Horn propagation from the ABox and TBox.
     Therefore `a` and `b` are merged in `harvested_base_comp` if and only if
     `O |= SameIndividual(a, b)`, and `C` appears in the label of `a` if and
     only if `O |= ClassAssertion(C, a)`.
   - When `used_choice_points > 0`, `SAME` and `TYPE` do not trust branch-dependent
     choices in `M_0`; they fall back to exact probe classification.

2. **`VALUE` (`ObjectPropertyAssertion` and `DataPropertyAssertion`)**:
   - Even when `used_choice_points == 0` in the hypertableau consistency pass,
     auxiliary existential fillers or disjunctive roleclauses in `M_0` are only
      guaranteed to hold in *some* model (`M_0`), unless every step in their
     derivation is deterministic Horn propagation from entailed facts.
   - **Negative bound (`ProvedNotValues` from `M_0`)**: Because `M_0` is a
     verified model of `O` closed under the RBox, any triple `(r, a, b)` (or
     data assertion `(p, a, lit)`) *absent* from `M_0` has a countermodel (`M_0`
     itself) and is therefore proved *not* entailed (`O |/= r(a, b)`).
   - **Positive bound (`proved_values` from `H_0`)**: `from_exported_model`
     constructs the minimal entailed Horn graph `H_0` over the individual
     equivalence classes, seeded strictly with facts known to hold in *all*
     models of `O`:
     - explicit source `ClassAssertion`, `ObjectPropertyAssertion`,
       `DataPropertyAssertion`, and `SameIndividual` axioms,
     - already-verified `realization.types` and `realization.same` rows, and
     - `classification.subsumptions` (`A <= B`, `A <= {o}`, `A <= exists r.{o}`,
       `A <= p value lit`).
     `H_0` is then saturated to a fixpoint under deterministic single-head Horn
     clauses (`body -> head` with `|head| == 1` and no fresh existential terms)
     and the full RBox (`sub_roles`, `inverses`, `symmetric`, `reflexive`,
     `transitive`, and `role_chains`). Every edge `(elem(a), r, elem(b))` in
     `H_0` holds in every model of `O` and is immediately emitted in
     `proved_values`.
   - **Residual gap (`residual_value_targets`)**: Any edge `(elem(a), r, elem(b))`
     present in `M_0` but absent from `H_0` (for example, an edge chosen by a
     disjunction `r(a, b) or s(a, b)` or induced by an equality merge from an
     at-most restriction) is placed in `residual_value_targets` and decided by
     exact probe classification (`__val_subj__` / `__val_obj__` in
     `residual_extension`). When every edge of `M_0` between named individuals
     is already in `H_0`, `residual_value_targets` is empty and `0` probes run.
   - **Reconstructed structures are not models (anonymous excursions).** The
     negative bound above needs `M_0` to be a model of `O`. That holds for the
     `ht-bridge` and `cb-horn` models read from the export, but not when the
     ABox was elided from the exported model (`abox_elided`, the usual case for
     `--values` without `--realize`) or on `el-canonical`: then
     `from_exported_model` rebuilds the named part from the source (ABox edges,
     class assertions, Horn saturation, at most three rounds of Skolem
     witnesses), and that structure is not a model. The earlier argument
     claimed that, without `ObjectHasValue`, `ObjectOneOf` and
     `ObjectHasSelf`, no edge between named individuals arises beyond the
     asserted ones and their RBox closure. That condition is wrong for
     composite roles: a path can leave a named individual into its anonymous
     tree and come back, and a role chain or a transitive role turns the path
     into a named edge. Example (`f9002_44`): `B(a4)`, `B ⊑ ∃s3⁻.B`,
     `s3⁻ ⊑ s1`, `s1` symmetric and `s1 ∘ s3 ⊑ c1` entail `c1(a4, a4)` through
     the anonymous `x` with `s3(x, a4)` and `s1(a4, x)`. KM lost the row
     because the fast path compared two structures that both lacked it.
     The upper bound is now `edge_set` plus `ExcursionBound`: each role that
     `named_role_bound::excursion_roles` reports, over every pair of named
     individuals in one component of the named edge graph (a single component
     when the source has a nominal edge or a merge into a nominal). The fast
     path is taken only when all those candidates are proved; otherwise every
     unproved candidate goes to the residual probes, which decide it exactly.
     *Argument.* A consistent `O` has a forest model `I`: the named
     individuals with their named edges, and under each a tree of anonymous
     elements, each created through one generating role (an existential or
     min-cardinality restriction, a negated universal or max-cardinality),
     with `HasSelf` loops, merges among the successors of a merging role
     (functional, inverse-functional, cardinality) and identifications with
     nominals. `excursion_roles` works on an abstraction with one node `N`
     for all named individuals and one node `X_t` per generating role `t`.
     Sending every element of `I` to its node is a homomorphism once the
     abstraction merges the successors of every merging role, and the RBox
     closure is monotone under homomorphisms. Each abstract fact carries a
     flag, set when its derivation used an edge at an anonymous node, so a
     named pair `r(a, b)` of `I` whose derivation needs an anonymous element
     maps to a flagged fact `(N, r, N)`, and `r` is reported. Its path enters
     and leaves anonymous trees only at named individuals joined by named
     edges, or through nominals, so `a` and `b` lie in one component. Every
     named edge of `I` is therefore in `edge_set` or a candidate, and a pair
     in neither has the countermodel `I`.
   - **Individuals outside the model.** The `ht-bridge` model holds only the
     individuals the ABox mentions; `from_exported_model` gave every other
     declared individual a stand-in element without classes or edges, so a
     row such as `s(x, x)` from `⊤ ⊑ ∃s.Self` (or `⊤ ⊑ ≤1 s0` derived from an
     inverse-functional `s0` with `s0⁻ ⊑ s0`) was lost for an individual `x`
     that occurs only in its declaration. Such an `x` is interchangeable with
     a fresh individual, so its rows are what the TBox gives every element:
     loops on the roles that `excursion_roles` reports when `HasSelf` and
     nominal roles also count at a named individual, and, when nominals
     occur, edges on those roles to and from any individual. Each such row
     that the Horn structure does not prove goes to the residual probes. When
     an individual that occurs in an axiom is missing from the model, or the
     source links anonymous individuals or uses the universal role,
     `from_exported_model` declines and the exact probe run answers.
   - **Named individuals forced equal (2026-11-21).** Horn rules can force
     two named individuals equal: a nominal domain (`t1` with domain `{a1}`
     and `t1(a0, a3)` gives `a0 = a1`), `⊤ ⊑ =1 s3` with domain `{a0}` (every
     individual equals `a0`), or `B ⊑ {o}`. The structure carries such
     merges only when `has_horn_merges` holds (elided ABox); otherwise it
     keeps the two elements apart, so it is not a model and both bounds miss
     the rows of the merged individuals (`g7002_0026` lost `t0(a1, a0)`,
     `f4104_41` lost 3,240 of 6,480 VALUE rows without `--realize`).
     `saturate_horn_in_place` now applies every Horn nominal merge
     (`[B(x)] -> [x = o]`, with or without the head `{o}`) to its union-find,
     and when two named elements end in one class without `has_horn_merges`,
     `from_exported_model` declines and the exact probe run answers.
   - **Bare individuals (2026-11-22).** An individual `a` that occurs only in
     its declaration, annotations and `ClassAssertion(A, a)` with named `A`
     (the set `S_a`) needs no value probe when every `SubClassOf`,
     `EquivalentClasses` and `DisjointClasses` axiom holds at a *bare*
     element: atomic classes exactly `S_a`, no successors, no data values
     (`∃`, `HasValue`, `HasSelf`, `OneOf` and `≥ n` with `n ≥ 1` are false
     there; `∀` and `≤ n` are true), all other axioms are property axioms or
     assertions about other individuals, and the source has no universal
     role, reflexive role, key or rule. Argument: take any model `I` of `O`,
     add a new bare element `x` and interpret `a` as `x`. No element has an
     edge to `x` and no nominal names `a`, so every other element keeps its
     truth values, `x` satisfies the TBox by the check, and `a`'s assertions
     hold; the result is a model of `O` in which `a` has no edge. So no row
     `r(a, y)` or `r(y, a)` is entailed, and `from_exported_model` drops the
     residual targets and sources of `a`. This removes the 112 excursion
     targets of `ore_ont_14012` (16 `oboInOwl#Subset` individuals, 7
     transitive or inverse roles), whose probe run had timed out.

3. **`DIFFERENT` (`DifferentIndividuals`)**:
   - Two individuals `a` and `b` that are distinct elements in `M_0`
     (`elem(a) != elem(b)`) are *not* automatically entailed to be different:
     `M_0` merely chose not to merge them. `O |= DifferentIndividuals(a, b)`
     holds if and only if *no* model of `O` merges `a` and `b` (equivalently,
     `O union {SameIndividual(a, b)}` is unsatisfiable).
   - **Positive bound (`proved_different` from `H_0 / (u = v)`)**: For each pair
     `(u, v)` with `u != v`, `from_exported_model` merges `u` and `v` inside the
     entailed graph `H_0` and saturates under deterministic Horn rules,
     functional/inverse-functional role cascades, keys, at-most cardinalities on
     provably distinct neighbours, functional data properties with distinct
     literals, class disjointness, negative property assertions, and nominal
     singletons. Because every fact in `H_0` holds in *every* model of `O`, a
     clash in `H_0 / (u = v)` proves that no model of `O` can identify `u` and
     `v`, so `(a, b)` is emitted in `proved_different`.
   - **What an element of `H_0` stands for (2026-11-21).** The argument above
     needs every element of `H_0` to name one term whose facts hold in every
     model: a named individual, or a Skolem term `f(u)` created for exactly
     that function at `u` while the existential's body is entailed at `u`.
     Every clash rule may then use the element as that term. In particular the
     min-cardinality rule `[M(x), f1(x) = f2(x)] -> []` concludes a clash from
     `find(w1) == find(w2)` only when `w1` and `w2` are the dedicated
     witnesses of `f1(u)` and `f2(u)`: if the Horn rules on `H_0 / (u = v)`
     force them equal, every model of `O ∪ {a = b}` has `f1(u) = f2(u)` and
     `M(u)`, which `O` forbids. An existing successor that only carries the
     filler classes may be reused to satisfy an existential, but it is not
     the term `f(u)` (a model may send `f(u)` elsewhere), so the code does not
     record it as a witness and no inequality clash rests on it. Before this
     rule the witness map pointed both functions of `≥ 2 s0.D` at one reused
     successor, so every merge touching that individual reported a clash and
     `--different` printed rows such as `DIFFERENT :a0 :a2` in
     `g7001_0022.ofn` that are not entailed (`O ∪ {a0 = a2}` is consistent).
     A pair whose clash cannot rest on such terms is `Undecided` and goes to
     the exact probe.
   - **Elements that merge individuals by choice (2026-11-22).** The
     element-level arguments read an element of `M_0` as one individual. An
     exported model may put several individuals into one element although
     their sameness is not entailed (a nominal cover `⊤ ⊑ {a8, a9}` forces a
     choice). An explicit `DifferentIndividuals(a9, a3)` then made the two
     elements different and every pair of their members was printed
     (`nc8302_0001.ofn`: 14 rows, 2 entailed; 2,225 rows not entailed in 750
     cover cases, all checked with `O + SameIndividual(a b)`). When some
     element holds individuals that `same_comp` does not prove equal, every
     pair now goes to the exact probe.
   - **Proved differences hold between classes (2026-11-22).** During the
     merge test an element of the union-find stands for its whole class. A
     merge of two classes clashes when any member of one is proved different
     from any member of the other, not only the two roots. Checking only the
     roots missed `DIFFERENT a2 a4` in `g8301_366.ofn` (after `a2 = a4`,
     `≤ 1 r1` at `a4` merges `a7`, and `a7 != a2` is asserted): the model
     side then reported the quotient as a model and the row was lost. In
     `H_0` the clash is sound because every merge in the class is entailed
     under `a = b` and every member difference is entailed.
   - **Negative bound (`ProvedNotDifferent` from `M_0 / (u = v)`)**: If `H_0 /
     (u = v)` does not clash, `from_exported_model` forms the quotient of the
     full exported model `M_0 / (u = v)` by identifying `u` and `v` in `M_0`,
     closing under congruence (functional roles, keys, and Horn clauses), and
     checking whether the resulting quotient satisfies *every* normalized clause,
     existential restriction, data-value restriction, negative assertion, and
     cardinality bound of `O` without triggering any unresolved disjunction or
     cardinality equality. When `M_0 / (u = v)` is a clash-free model of
     `O union {SameIndividual(a, b)}`, it is a countermodel to
     `DifferentIndividuals(a, b)`, proving `O |/= DifferentIndividuals(a, b)`.
   - **Residual gap (`residual_different_pairs`)**: Any pair `(a, b)` that
     neither clashes in `H_0 / (u = v)` nor yields a verified quotient model
     `M_0 / (u = v)` is placed in `residual_different_pairs` and decided by the
     exact probe reduction (`SubClassOf({a}, __diff_b)` / `DisjointClasses({b}, __diff_b)`
     in `residual_extension`).

---

## Routes, terminal state reuse, and witness probe bounds

### 1. EL canonical model (`route: "el-canonical"`)

Applies to the `elc` route, the `flat_nf1` source fast path, and any route that
finishes in EL++ completion (including positive ABoxes materialised into EL
completion and non-EL residual clauses certified by `check_certificate`).

- **State held at the end of the answering run**:
  - In `elcomplete` (`classify_inner_mode`, `acyclic_nf1_taxonomy`, and
    `positive_abox_classify_mode`), the completion holds `contexts` (each named
    or structural concept and `⊤`), `sub_super[c]` (the saturated subsumer bitset
    or vector of context `c`), and `edges[c]` (the saturated role-successor list
    `(role, target_ctx)` of context `c`).
  - In `flat_nf1` (`classify_reader` and `classify_sparse_horn_reader`), the
    answering scan holds `names`, `role_names`, the NF1 superclass graph
    `outgoing`, conjunction rules `union_rules`, existential leaves
    `existentials`, `rbox_rows`, and the ABox assertions (`class_assertions`,
    `existential_assertions`, `individuals`).
- **How the export is read off**:
  - One domain element is emitted per satisfiable context (`⊤`, each satisfiable
    class, and each named-individual equivalence class `__nom__a`), with
    `classes` read directly from `sub_super[c]` (or the `outgoing`/`union_rules`
    closure in `flat_nf1`) and `edges` read from `edges[c]` (or `existentials`),
    closed under `rbox_rows`.
- **Additional witness probes required**: **0**. Every satisfiable class already
  has its own canonical context in the terminal completion state.
- **Soundness and witness exactness**: By the canonical-model theorem for EL++
  completion, this finite structure satisfies all normalized EL++ clauses (and
  all residual clauses when `check_certificate` passes), requires no blocking,
  and satisfies `B in classes(e_A)` if and only if the ontology entails
  `A <= B`. Every witness has `"exact": true`.

#### Example (`el-canonical`)

Source ontology:
```owl
Prefix(:=<http://example.org/>)
Ontology(
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  Declaration(ObjectProperty(:r))
  SubClassOf(:A ObjectSomeValuesFrom(:r :B))
  SubClassOf(ObjectSomeValuesFrom(:r :B) :C)
)
```

Exported JSON lines:
```json
{"kind":"model","format":"km-model-v1","status":"ok","route":"el-canonical","elements":4,"edges":2,"closure":"none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)","witness_exact":true,"blocked":0}
{"kind":"element","id":"e0","context":"⊤","classes":[]}
{"kind":"element","id":"e1","context":"http://example.org/A","classes":["http://example.org/A","http://example.org/C"]}
{"kind":"element","id":"e2","context":"http://example.org/B","classes":["http://example.org/B"]}
{"kind":"element","id":"e3","context":"http://example.org/C","classes":["http://example.org/C"]}
{"kind":"edge","role":"http://example.org/r","from":"e1","to":"e2"}
{"kind":"witness","class":"http://example.org/A","element":"e1","exact":true}
{"kind":"witness","class":"http://example.org/B","element":"e2","exact":true}
{"kind":"witness","class":"http://example.org/C","element":"e3","exact":true}
```

---

### 2. Native hypertableau bridge (`route: "ht-bridge"`)

Applies to ontologies classified by the native Konclude hypertableau bridge
(`ht_bridge`, `ht_full`, `nominal_ni_abox`, `symbolic_source`, and the bridge
arm of `production_all`).

- **State held at the end of the answering run**:
  - During `bridged_classify_opts_with_trigger_absorption_inner`, the bridge
    retains its shared `CompletionTaskHandleAlgorithm`,
    `CalculationAlgorithmContextBase`, `Bridged` arena, the retained
    deterministic consistency base (`retained_consistency_databox`), and the
    saturation/satisfiable-expander caches (`sat_node`s and
    `sat_node_ext_linked_role_successor_hash` in `ctx.process_context()`).
  - When `--export-model` is active, the answering run harvests the consistency
    completion component (`harvested_base_comp`) at the end of
    `native_nominal_consistency`, harvests the root-connected components of
    every subject `s` whose satisfiability or batch/pairwise refutation probe
    ran during Phase 1 or Phase 2 (`harvested_subject_comps[s]`), and collects
    linked role-successor hashes across all completed saturation nodes.
- **How the export is read off**:
  - `finish_bridge_export_model_from_live_state` starts from `harvested_base_comp`
    (or one `bridged_top_satisfiable` read-off on the live context when no
    nominal consistency pass ran) and merges `harvested_subject_comps` and
    sufficient saturation subgraphs (`extract_saturation_subject_component`),
    sharing nominal nodes (`rep_id < 0`) with the base consistency component and
    expanding saturation-blocked or backend-blocked nodes
    (`PRF_SATURATIONBLOCKINGCACHED`,
    `PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED`,
    `PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED`) directly from
    `sat_node_ext_linked_role_successor_hash`. Lazy `CCEQ` definitions
    `A == D` are evaluated in topological order on nodes where neither `+A` nor
    `-A` was expanded.
- **Additional witness probes required and how they are bounded**:
  - Subjects answered by the saturation prepass (`answered_sat`) are extracted
    directly from the saturation graph (`s07_concept_reference_node`) with zero
    completion probes whenever their reachable saturation subgraph is
    sufficient. Subjects answered by KPSet graph propagation are first matched
    against existing elements of the consistency, saturation, and harvested
    completion components.
  - Let `S_missing` be the satisfiable named classes whose harvested/saturation
    components still contain unseparated non-entailed superclasses. Each
    residual probe restores the retained consistency base (`renew_env`) with
    production completion blocking and saturation coupling enabled (`satcache`),
    rather than rebuilding the terminology or running uncached completion. For
    covering-union classes `s <= d1 or d2`, single-disjunct branch probes emit
    covering witness elements so their intersection equals the entailed
    superclasses of `s`.
  - The residual probe loop checks `export_deadline` (`--export-model-budget`,
    default `1x classify_time + 2 s`) before every probe. If the deadline is
    reached, the loop stops immediately and returns the consistency model plus
    all witnesses found so far with `"status": "partial"` and `"reason"` naming
    the budget and completed probe count.

#### Example (`ht-bridge`)

Source ontology:
```owl
Prefix(:=<http://example.org/>)
Ontology(
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  SubClassOf(:A ObjectUnionOf(:B :C))
)
```

Exported JSON lines:
```json
{"kind":"model","format":"km-model-v1","status":"ok","route":"ht-bridge","elements":4,"edges":0,"closure":"none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)","witness_exact":false,"blocked":0}
{"kind":"element","id":"e0","context":"⊤","classes":[]}
{"kind":"element","id":"e1","context":"http://example.org/A","classes":["http://example.org/A","http://example.org/B"]}
{"kind":"element","id":"e2","context":"http://example.org/B","classes":["http://example.org/B"]}
{"kind":"element","id":"e3","context":"http://example.org/C","classes":["http://example.org/C"]}
{"kind":"witness","class":"http://example.org/A","element":"e1","exact":false}
{"kind":"witness","class":"http://example.org/B","element":"e2","exact":true}
{"kind":"witness","class":"http://example.org/C","element":"e3","exact":true}
```

---

### 3. Consequence-based Horn context graph (`route: "cb-horn"`)

Applies to the CB route (`cb_plain*`, `cb_trigger*`, `cb_role_guard*`,
`nominals`, and `--cb`).

- **State held at the end of the answering run**:
  - At the end of `Reasoner::saturate_inner`, each saturation shard holds an
    `Engine` with `contexts` (the root context `⊤`, each query context `C`, and
    each created successor context `Succ(preds)`), `worked_off(ctx)` (all
    saturated clauses of `ctx`), `successors(ctx)` (edges `(f, target_ctx)`),
    and `mutual_unit_groups` (collapsed 2-cycles of equivalent unit concepts).
- **How the export is read off**:
  - Before `Reasoner::saturate_inner` drops each shard's `Engine`,
    `Engine::extract_cb_export_shard` inspects `worked_off(ctx)`. If any
    satisfiable context holds an unreduced body-free multi-literal head clause
    (`⊤ -> A(x) | B(x)` where no head literal holds as a unit fact in that
    context), `extract_cb_export_shard` declines in under 1 ms. Otherwise it
    extracts `CbContextNode`s from the shard.
  - `build_cb_export_model_from_shards` merges the shards, restores
    `mutual_unit_groups` concept aliases, links `(u, r, v)` across
    `ctx.successors[f]`, closes edges under the RBox in `O(|RBox| * |edges|)`
    via role-indexed adjacency lists, and verifies all normalized clauses using
    inverted concept and role indexes under `export_deadline`.
- **Additional witness probes required**: **0**. Every satisfiable named class is
  already a root query context in one of the saturated CB shards (or an alias
  in `mutual_unit_groups`).
- **Source reductions and projections**:
  - `omit_separable_abox` (`positive_abox_tbox_separable`,
    `atomic_class_abox_candidate`, `existential_witness_abox_candidate`,
    `inert_role_abox_probe_candidate`), `abox_quotient`,
    `positive_abox_quotient`, `data_abox_projection`, and `mirror` record their
    reduction metadata during classification and reconstruct the ABox
    individuals, projected data values, or private negative-existential mirrors
    directly on top of the answering route's model in `apply_post_hooks`,
    requiring **0** additional solver runs.
- **When the CB context graph is a model of the Horn part and when it is not**:
  1. *When it is a model*: On Horn DL-clauses without equality in clause heads
     (clauses of the form `B1(x) & ... & Bn(x, z) -> C(x)`, `-> r(x, f(x))`,
     `-> C(f(x))`, or `B1 & ... -> bottom`), every worked-off consequence of a
     context core is a unit clause `⊤ -> L` in that context (once predecessor
     triggers are resolved). With all successor triggers armed, every derived
     existential `⊤ -> r(x, f(x))` has a target context `v = ctx.successors[f]`
     seeded with all unit filler facts `C(x)` pushed along `f`, and `Pred`
     propagates backward consequences `r(y, x) & D(x) -> E(y)` back to the
     predecessor context. The unit-fact graph therefore satisfies all Horn
     clauses, and `B in classes(ctx_A)` holds if and only if `⊤ -> B(x)` is
     derived in `ctx_A` (exact witnesses). The same holds on non-Horn ontologies
     whose disjunctive or equality clauses happen to be satisfied by the unit
     facts of every context (for example, when one disjunct is already entailed
     by the Horn core of every context that triggers the clause body).
  2. *When it is not a model*:
     - **Unsplit disjunctions**: When a context derives a multi-literal
       disjunctive clause `⊤ -> B(x) | C(x)` without deriving either `⊤ -> B(x)`
       or `⊤ -> C(x)` as a unit fact, neither `B` nor `C` is in the context's
       unit-fact label, so the unit-fact interpretation falsifies `B(x) | C(x)`.
     - **Non-trivial equality / functionality / at-most restrictions**: When a
       clause head contains an equality `y1 = y2` (such as `FunctionalObjectProperty`
       or `ObjectMaxCardinality`) and a context creates two distinct successor
       contexts `v1 != v2` for the same role `r`, the CB calculus transfers
       concept facts between `f1(x)` and `f2(x)` via the `Eq` rule `⊤ -> f1(x) = f2(x)`
       inside the parent context, but keeps `v1` and `v2` as distinct context
       ids unless quotiented; or if `y1 = y2` appears in a disjunction, the
       distinct elements violate the cardinality bound.
     - **Nominals in non-nominal contexts**: If `C <= {a}` derives `__nom__a(x)`
       in the context of a satisfiable class `C` distinct from `{a}`, interpreting
       each context as a distinct element would place the singleton individual
       `a` in two elements.
  - **Verification and decline**: `cb_model` evaluates every normalized clause
    of the ontology on the extracted unit-fact structure before exporting. If
    any clause is violated (or if nominals, SWRL rules, or cardinalities cannot
    be represented as a valid model), `cb_model` declines and writes a
    `"status": "declined"` record with the reason.

#### Example (`cb-horn`)

Source ontology:
```owl
Prefix(:=<http://example.org/>)
Ontology(
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  Declaration(ObjectProperty(:r))
  SubClassOf(:A ObjectSomeValuesFrom(:r :B))
  SubClassOf(:B :C)
  SubClassOf(ObjectSomeValuesFrom(:r :C) :D)
  Declaration(Class(:D))
)
```

Exported JSON lines:
```json
{"kind":"model","format":"km-model-v1","status":"ok","route":"cb-horn","elements":6,"edges":1,"closure":"none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)","witness_exact":true,"blocked":0}
{"kind":"element","id":"e0","context":"⊤","classes":[]}
{"kind":"element","id":"e1","context":"http://example.org/A","classes":["http://example.org/A","http://example.org/D"]}
{"kind":"element","id":"e2","context":"http://example.org/B","classes":["http://example.org/B","http://example.org/C"]}
{"kind":"element","id":"e3","context":"http://example.org/C","classes":["http://example.org/C"]}
{"kind":"element","id":"e4","context":"http://example.org/D","classes":["http://example.org/D"]}
{"kind":"element","id":"e5","context":"__cb_ctx_5","classes":["http://example.org/B","http://example.org/C"]}
{"kind":"edge","role":"http://example.org/r","from":"e1","to":"e5"}
{"kind":"witness","class":"http://example.org/A","element":"e1","exact":true}
{"kind":"witness","class":"http://example.org/B","element":"e2","exact":true}
{"kind":"witness","class":"http://example.org/C","element":"e3","exact":true}
{"kind":"witness","class":"http://example.org/D","element":"e4","exact":true}
```

---

## Using the Exported Model for ABox Queries (`--values` and `--different`)

When `km classify` runs with `--values` or `--different`, `orchestrate::abox_rows::from_exported_model` uses the consistency model `M_0` (`raw.base_labels` / `raw.base_edges` on `ht-bridge`, or `raw.labels` / `raw.edges` on `cb-horn` and `el-canonical`) to compute a sound lower bound (`proved_values`, `proved_different`) and a sound upper bound (`edge_set`, unrefuted pairs) before running any residual exact probe classification.

### 1. When Deterministic Consistency Completion Is Sufficient for `VALUE` on `ht-bridge` (P2)

For a consistent ontology `O`, two named individuals `a, b`, and a named object property `r`, `O` entails `r(a, b)` if and only if `(a^M, b^M) in r^M` holds in every model `M` of `O`. Let `M_0` be the consistency completion model extracted from `ht-bridge`, and let `Horn(O)` be the deterministic 1-head Horn consequence set computed on the explicit `SameIndividual` equivalence classes of `O` by iterating:

1. explicit `ObjectPropertyAssertion(r, a, b)` and `ReflexiveObjectProperty(r)` edges;
2. `ObjectHasSelf(r)` and `ObjectHasValue(r, target)` rules triggered by entailed classes of each individual;
3. RBox closure (`close_edges_under_rbox_rows`: sub-roles, inverses, symmetry, transitivity, and role chains);
4. `ObjectPropertyDomain(r, C)`, `ObjectPropertyRange(r, C)`, and `DataPropertyDomain(p, C)` propagation into entailed individual classes, followed by class subsumption closure and re-evaluation of steps 2--4 to fixpoint; and
5. 1-head Horn normalized DL-clauses and Skolem existential witness materialization (`saturate_horn_in_place`).

Every edge in `Horn(O)` holds in all models of `O` by soundness of the Horn rules, and every edge entailed by `O` holds in the specific model `M_0`, provided `M_0` is a model. On `ht-bridge` and `cb-horn` with the ABox in the export it is. When the ABox was elided or the route is `el-canonical`, `M_0` is a structure rebuilt from the source and the right-hand side below is `{ r(a, b) | M_0 |= r(a, b) }` together with the anonymous-excursion candidates of `ExcursionBound` (see "Reconstructed structures are not models" above); without them the inequality fails for role chains and transitive roles through anonymous elements (`f9002_44`):

```text
Horn(O)  <=  { r(a, b) | O |= r(a, b) }  <=  { r(a, b) | M_0 |= r(a, b) }
```

This sandwich inequality characterizes when a single consistency completion `M_0` on `ht-bridge` decides `VALUE` without residual probes:

- **Sufficiency condition (0 residual probes)**: When `M_0` performs no non-Horn nominal merge (every element `u` of `M_0` contains named individuals from at most one explicit `SameIndividual` equivalence class) and every named-individual role edge in `M_0` belongs to `Horn(O)` (`{ r(a, b) | M_0 |= r(a, b) } == Horn(O)`), the lower and upper bounds coincide. Then `Horn(O)` is the exact set of entailed `VALUE` rows and no probe run is needed.
- **Residual probe fallback**: A role edge `(a, r, b)` can hold in `M_0` without belonging to `Horn(O)` only when `M_0` made a nondeterministic branch choice that affects named-individual edges:
  1. a nondeterministic nominal merge in `M_0` (for example, `a in C` with `C == ObjectOneOf(b_1, ..., b_k)`, where `ht-bridge` merges `a` with `b_i` in `M_0`, as on `ore_ont_6822`),
  2. a disjunctive role or concept choice along a chain between named individuals, or
  3. an at-most or functional cardinality merge between role successors.
  Whenever `M_0` merges individuals from distinct `SameIndividual` components onto the same element, `from_exported_model` computes `proved_values = Horn(O)` on the unmerged `SameIndividual` components and places every edge in `{ r(a, b) | M_0 |= r(a, b) } \ Horn(O)` into `residual_value_targets` and `residual_value_sources`. The orchestrator then runs the exact probe reduction `P_a <= exists r. P_b` on those residual candidates.

### 2. Soundness and Completeness of `DIFFERENT` via Merged-Pair Horn Saturation (P1)

For a consistent ontology `O` and two named individuals `a, b`, `O` entails `a != b` if and only if `O union { a = b }` is inconsistent.

1. **Constructive difference (`proved_different`)**: `from_exported_model` records `a != b` as constructively proved when `a` and `b` are separated in `Horn(O)` by an explicit `DifferentIndividuals` axiom, a `NegativeObjectPropertyAssertion(r, a, b)` coupled with an entailed `r(a, b)` edge (or an entailed `r(a, b)` on an `IrreflexiveObjectProperty(r)`), a `NegativeDataPropertyAssertion(p, a, v)` coupled with an asserted `p(b, v)`, disjoint entailed classes `C(a)` and `D(b)`, or distinct literals on a `FunctionalDataProperty`.
2. **Model-quotient non-difference certificate**: For each remaining pair `(u, v)` with `u != v` in `M_0` (when the ontology has no unhandled non-Horn clauses), `from_exported_model` forms the quotient structure `M_0 / (u = v)` by merging `u` and `v`, runs `saturate_horn_in_place` to fixpoint (propagating multi-conjunct concept rules, universal restrictions across Skolem existential witnesses, functional object/data role cascading merges, and cardinality checks), and tests whether the saturated quotient satisfies all normalized clauses and cardinalities of `O` without a clash. If `M_0 / (u = v)` is a valid model of `O union { u = v }`, then `O` does not entail `u != v` and the pair is pruned.
3. **Exact probe test on residual pairs**: Every pair not constructively proved different in step 1 and not certified consistent by `M_0 / (u = v)` in step 2 is placed in `residual_different_pairs` and tested by the exact probe reduction `ObjectIntersectionOf(P_a P_b) <= owl:Nothing`.

