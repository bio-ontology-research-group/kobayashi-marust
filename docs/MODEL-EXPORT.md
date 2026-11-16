# Model export (`km classify --export-model FILE`)

Status: implemented on the `el-canonical`, `ht-bridge`, and `cb-horn` routes.

`km classify --export-model FILE` writes a finite representation of a model of
the input ontology over source-level IRIs after classification finishes. The
export path runs after standard classification output is published, so it never
alters classification results and adds zero overhead when `--export-model` is
omitted.

## JSON lines format (`km-model-v1`)

Each line is a JSON object with a `"kind"` field. All class, role, data
property, and individual names are expanded to full source IRIs (internal
normalizer symbols such as `Q_*`, `__def__*`, and `__trig__*` are stripped).

1. **Header (`"kind": "model"`)**
   - Consistent ontology:
     ```json
     {"kind":"model","format":"km-model-v1","status":"ok","route":"el-canonical","elements":3,"edges":1,"closure":"none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)","witness_exact":true,"blocked":0}
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

## Routes and semantics

### 1. EL canonical model (`route: "el-canonical"`)

Applies to the `elc` route and to any route that finishes in EL++ completion
(including positive ABoxes materialised into EL completion and non-EL residual
clauses certified by `check_certificate`).

- **Construction**: One element per satisfiable concept context in the
  saturated EL completion state (`⊤`, each satisfiable named or structural
  concept, and each equivalence class of named individuals `__nom__a`), with
  `classes` read from `sub_super[c]` and `edges` read from `edges[c]` (closed
  under the RBox).
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
(`ht_bridge`, `ht_shoq`, `ht_general`, `ht_full`, `nominal_ni_abox`, and the
bridge arm of `production_all`).

- **Construction**: First runs the ontology consistency completion
  (`native_nominal_consistency` when nominals or ABox individuals are present,
  or `bridged_top_satisfiable` otherwise) and extracts all live unmerged
  representative nodes, their positive concept tags, their role links, and any
  direct/signature blocking pairs `(element, blocker)`. Next, for each
  satisfiable named class `C` not already witnessed with exact superclasses in
  the model, runs a rooted completion for `C` (refining with negated non-entailed
  classes when a single branch picked an avoidable supertype) and appends its
  connected component, sharing nominal elements with the consistency component.
  Lazy `CCEQ` definitions `A == D` are evaluated in topological order on nodes
  where neither `+A` nor `-A` was expanded.

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

Applies to the CB route (`cb_plain*`, `cb_trigger*`, `cb_role_guard*`, and
`--cb`).

- **Construction**: Runs the CB engine with successor triggers enabled for all
  concepts and roles so every derived unit existential `⊤ -> r(x, f(x))` /
  `⊤ -> C(f(x))` materialises its successor context `ctx.successors[f]`. Each
  satisfiable root or reachable successor context becomes a domain element; its
  `classes` are the unit concept facts `⊤ -> C(x)` worked off in that context
  (plus its core), and its `edges` are the unit role facts `⊤ -> r(x, x)`,
  `⊤ -> r(x, f(x))`, and `⊤ -> r(f(x), x)` across `ctx.successors[f]`, closed
  under the RBox.
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
