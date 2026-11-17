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
   {"kind":"element","id":"e1","context":"http://example.org/A","classes":["http://example.org/A","http://example.org/B"],"individuals":["http://example.org/a"]}
   ```
   `classes` lists the source classes that hold at `id`. `individuals` (omitted
   when empty) lists the named individuals interpreted by `id`.

3. **Object-property edges (`"kind": "edge"`)**
   ```json
   {"kind":"edge","role":"http://example.org/r","from":"e1","to":"e2"}
   ```
   Edges are closed under the RBox (sub-roles, inverse roles, symmetric roles,
   reflexive roles, transitive roles, and role chains).

4. **Data-property values (`"kind": "value"`)**
   ```json
   {"kind":"value","element":"e1","property":"http://example.org/p","cell":"__dt__val__\"1\"^^xsd:integer","datatypes":["__dt__integer","__dt__val__\"1\"^^xsd:integer"],"literal":"\"1\"^^xsd:integer"}
   ```

5. **Merged individuals (`"kind": "same"`)**
   ```json
   {"kind":"same","individuals":["http://example.org/a","http://example.org/b"],"element":"e1"}
   ```
   Emitted whenever two or more named individuals denote the same domain
   element.

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
   Maps each satisfiable named class `C` to an element `e` in whose `classes`
   list `C` appears. When `"exact": true`, the source classes of `e` equal the
   entailed named superclasses of `C` (`{D | O |= C <= D}`). When `"exact":
   false` (for example, when `C <= D1 or D2` without entailing either disjunct
   alone), `e` satisfies all entailed superclasses of `C` plus the chosen
   branch disjunct.

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
    saturation/satisfiable-expander caches.
  - When `--export-model` is active, the answering run harvests the consistency
    completion component (`harvested_base_comp`) at the end of
    `native_nominal_consistency` and harvests the root-connected component of
    every subject `s` whose satisfiability read-off probe ran during Phase 1
    (`harvested_subject_comps[s]`), before `renew` resets the context for the
    next subject.
- **How the export is read off**:
  - `finish_bridge_export_model_from_live_state` starts from `harvested_base_comp`
    (or one `bridged_top_satisfiable` read-off on the live context when no
    nominal consistency pass ran) and merges `harvested_subject_comps`, sharing
    nominal nodes (`rep_id < 0`) with the base consistency component and
    extracting root-connected anonymous nodes (`rep_id >= 0`) via BFS along
    `node_successor_iterator` and `blocker_individual_node`. Lazy `CCEQ`
    definitions `A == D` are evaluated in topological order on nodes where
    neither `+A` nor `-A` was expanded.
- **Additional witness probes required and how they are bounded**:
  - Subjects answered purely by the saturation prepass (`answered_sat`) or by
    KPSet graph propagation (`is_result_satisfiable_derivated`) did not run a
    completion read-off probe during Phase 1. Many of these are already
    witnessed on existing elements of the consistency or harvested subject
    components (`exact_witness_for` / `any_witness_for`).
  - Let `S_missing` be the satisfiable named classes that have no witness (or
    no exact witness) in the already harvested components. At most
    `|S_missing| <= |S_sat|` probes are needed, each restoring the retained
    consistency base (`renew_env`) rather than rebuilding the terminology or
    re-running ABox consistency. Each class `s in S_missing` runs at most 1
    read-off probe plus at most 1 refinement probe (seeding `+s` and `-d` for
    non-entailed superclasses `d` that appeared on the first branch).
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
