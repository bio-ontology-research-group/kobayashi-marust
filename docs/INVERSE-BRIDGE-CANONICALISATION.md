# Canonicalising inverse-role bridges in the EL completion

Audit of the proposal to remove inverse-role bridge expansion from
`engine/src/elcomplete.rs`: for a proven inverse pair `S ≡ R⁻`, rewrite every
`S(x,y)` to `R(y,x)`, delete the now-tautological bridge clauses, and support
the resulting reverse-oriented NF3/NF4 rules without materialising inverse
edges. Target ontology is ORE 1194.

## Verdict

The rewrite is sound. It does not help, and no lazy or symbolic representation
of the same rules helps, because the obstacle is not the mirror edges and not
the bridge clauses. It is that `elcomplete.rs` gives a filler concept and its
existential witness the same node, so a reverse-oriented rule has nowhere to
write a conclusion except into the published taxonomy.

Three separate statements, in decreasing generality:

1. **The rewrite is conservative.** If both bridge clauses are present, the
   substitution `S(x,y) := R(y,x)` preserves truth in every model, both bridges
   become tautologies, and named-class entailment is unchanged. Section
   "The rewrite is sound" proves this and gives the conditions under which the
   bridges may be deleted.
2. **The rewrite buys nothing.** It replaces 2 bridge clauses per pair with one
   reverse-oriented occurrence of every rule the dropped role carried: 55,721
   rules on ORE 1194 at the cheapest orientation, of which 10,418 are reverse
   existentials. `to_nf` refuses exactly those two wirings today, on purpose.
3. **Reverse-oriented rules cannot run on this node space at all.** The node
   for filler concept `B` is at once the witness of every `A ⊑ ∃R.B` and the
   named class `B`. Firing `∃R⁻.C ⊑ D` there is, literally, asserting the axiom
   `B ⊑ D`, which is not entailed. Any implementation that fires reverse rules
   against `sub_super` therefore over-derives rather than merely storing more,
   which is the reading the eager prototype's 14 GB fits. Test
   `a_reverse_rule_at_a_shared_witness_would_assert_a_named_subsumption`
   pins the counter-model. The prototype itself was not available for
   inspection, so this is a claim about the node space, not a code review.

Statement 3 also settles the relevance question. A relevance fence would have
to keep inverse consequences away from named classes, but on this node space
every node **is** a named class, so there is no internal region to fence. The
negative reachability result (NF4 heads reach 64,222 to 70,231 of 70,231 named
classes) is a symptom; the cause is node identity, and no tightening of the
reachability analysis changes it.

The one thing the mirror can still do soundly is prove itself **inert**: close
the bridges over the base structure and check that no named class gains a
subsumer or loses its witness. That is a model-side upper bound and it is what
the uncommitted virtual-mirror prototype on branch `codex/opus-1194-bridge`
does. It does not close 1194: the residual relevance certificate built on the
same idea was measured on 2026-08-01 at 132.9 s / 3.79 GiB, exit 3, reporting
`mirrored edge would add concept 359875 at node 236226` over virtual role
`BFO_0000050`. The bound is genuinely not tight.

**Recommendation.** Do not implement canonicalisation in `elc`. If the certified
EL route is attacked again for ORE 1194, the change that matters is splitting
the node space (witness nodes distinct from class nodes) plus a
universal-predecessor guard, which is the beginning of a Horn-ELI
consequence-based completion. That calculus already exists in `engine.rs`. The
cheap measurement that decides whether the split is worth building is in
"What would have to change".

## Where bridges come from and where they land today

The frontend emits `InverseObjectProperties(R,S)` and `ObjectInverseOf` as a
swapped role inclusion `R(x,y) → S(y,x)`. `to_nf` matches role inclusions only
when the head wiring equals the body wiring, so a swapped head falls to the
residual (`engine/src/elcomplete.rs`, the `role inclusion` branch). The residual
certificate then evaluates the clause against the canonical model, where it is
violated once per `R`-edge.

`is_pure_el_shape` mirrors the same refusal, so the automatic router never sends
a bridged ontology to the cert-off EL worker.

## Census of ORE 1194

`engine/py/role_census.py` classifies every clause with the same branch
structure as `to_nf` and reports, per role, which normal form the role lands in.
Input `/tmp/1194.clauses.json`, SHA-256
`5c0fdb40e5252e1d3092127bbe77c4cba74abf9da27041767f5c2959c2bc7da0`,
1,062,240 clauses, 151 roles. Full output in
[`../results/benchmarks/2026-08-02-1194-inverse-bridge-census/`](../results/benchmarks/2026-08-02-1194-inverse-bridge-census/ore_ont_1194.role_census.txt).

| clause kind | count |
| --- | --- |
| NF4 `∃R.C ⊑ D` | 410,281 |
| NF1/NF2 | 391,047 |
| existential halves (NF3) | 130,303 |
| residual | 203 |
| NF6 `R ⊑ S` | 48 |
| domain `∃R.⊤ ⊑ D` | 35 |
| inverse bridge | 14 |
| NF5 `A ⊑ ⊥` | 6 |
| NF7 role chain | **0** |

Bridge structure: 14 clauses, 6 reciprocal pairs (12 clauses) and 2 one-way
bridges.

| half A | positions | half B | positions |
| --- | --- | --- | --- |
| `BFO_0000050` | nf3 28,826, nf4 144,130, nf6\_sup 10 | `BFO_0000051` | nf3 10,256, nf4 45,127, nf6\_sup 1 |
| `RO_0002202` | nf3 28,826, nf4 144,130 | `RO_0002203` | nf3 102, nf4 107 |
| `distally_connected_to` | nf3 37, nf4 37 | `proximally_connected_to` | nf3 56, nf4 56 |
| `surrounded_by__uberon` | nf3 32, nf4 32 | `surrounds` | nf3 20, nf4 20 |
| `BSPO_0000098` | nf3 4, nf4 12 | `BSPO_0000102` | nf3 2, nf4 6 |
| `BSPO_0000124` | nf3 1, nf4 1 | `BSPO_0000125` | nf3 1, nf4 1 |

| one-way bridge | body role occurs elsewhere? |
| --- | --- |
| `has_distal_part(x,y) → distal_part_of(y,x)` | no: `bridge_base` only |
| `has_proximal_part(x,y) → proximal_part_of(y,x)` | no: `bridge_base` only |

Facts that fall out of the census and matter for the gates:

- **No bridged role has a residual, ground, or chain occurrence.** All 203
  residual clauses are disjunctions, cardinality, ranges and disjointness over
  unbridged roles, so the residual and cardinality gates are vacuous on 1194.
- **NF7 is empty for the whole ontology.** 1194 declares transitive roles and
  role chains, but the frontend compiles them into `__trans__R__C` and
  `__chain__R__C` marker concepts, which are ordinary NF4. A chain gate written
  against `idx.nf7_by_pair` (as in the `codex/opus-1194-bridge` prototype) is
  therefore vacuous here and protects nothing on this ontology. The markers are
  still ordinary NF4, so the NF4 treatment covers them, but the gate must not be
  advertised as covering chains.
- **Transitivity markers exist for `BFO_0000050` (28,826), `RO_0002202`
  (28,826), `BFO_0000051` (10,256), `BSPO_0000098` (4), `BSPO_0000102` (2) and
  ten smaller roles, but not for `RO_0002203`.** `RO_0002203 ≡ RO_0002202⁻` and
  the inverse of a transitive role is transitive, so canonicalising
  `RO_0002203 := RO_0002202⁻` would hand it the missing markers. That is a
  completeness gain from the rewrite, not a cost.
- **This capture contains no `ind` or `aux` terms at all** (3,110,619 `var` and
  260,660 `fun` terms). The ground-assertion gate is untested by it. The
  221,086 class assertions recorded in `HARD-RESIDUAL-AUDIT.md` are not in this
  clause file, so a nominal capture must be re-censused before the ground gate
  is trusted.

### Orientation is nearly free, and that is the point

For a reciprocal pair either half may be kept. The census reports both
directions:

| drop | keep | rules that become reverse-oriented |
| --- | --- | --- |
| `BFO_0000051` | `BFO_0000050` | 55,384 |
| `BFO_0000050` | `BFO_0000051` | 172,966 |
| `RO_0002203` | `RO_0002202` | 209 |
| `RO_0002202` | `RO_0002203` | 172,958 |
| `proximally_connected_to` | `distally_connected_to` | 115 |
| `distally_connected_to` | `proximally_connected_to` | 77 |
| `surrounds` | `surrounded_by__uberon` | 40 |
| `surrounded_by__uberon` | `surrounds` | 64 |
| `BSPO_0000102` | `BSPO_0000098` | 8 |
| `BSPO_0000098` | `BSPO_0000102` | 16 |
| `BSPO_0000125` | `BSPO_0000124` | 3 |
| `BSPO_0000124` | `BSPO_0000125` | 3 |

Cheapest orientation across the six pairs: **55,721 reverse-oriented rules**, of
which **10,418 are reverse existentials**. Worst orientation: 346,122.

The 6.2x spread is misleading as a cost model, and the correct reading is worth
stating because it removes an obvious tuning idea. After canonicalisation the
kept role carries the union `edges(R) ∪ transpose(edges(S))` whichever half is
kept, so the edge volume is orientation-independent, and the total rule count
(forward plus reverse) is the sum over both halves either way. Orientation only
decides which half is answered through the backward index `in_edges` rather
than the forward `edges`. Both indexes exist. So picking the cheap orientation
is not a lever that turns a timeout into a completion, and the eager
prototype's result would not have improved much by choosing better.

## The rewrite is sound

Let `Φ` contain both bridges `β₁ = R(x,y) → S(y,x)` and `β₂ = S(x,y) → R(y,x)`.
Then `Φ ⊨ ∀x,y. S(x,y) ↔ R(y,x)`, so `S^I = (R^I)⁻¹` in every model `I` of `Φ`.

Let `σ` replace role atoms `S(t₁,t₂)` by `R(t₂,t₁)`. For any model `I` of `Φ`
and any clause `c`, `I ⊨ c` iff `I ⊨ σ(c)`, because the two differ only by
atoms with identical truth values under `I`. Hence:

- **Partial rewriting is always safe.** Replacing any subset of `S`-occurrences
  keeps the model class unchanged. No gate is needed for this step.
- **Deleting the bridges requires totality.** `σ(β₁)` and `σ(β₂)` are both
  `R(x,y) → R(x,y)`, so both may be dropped, but only once `S` occurs nowhere
  else. If any `S`-occurrence survives, deleting the bridges disconnects it from
  `R` and changes the model class in both directions.
- **Named-class entailment is preserved.** `σ(Φ)` has no `S`. Every model `I'`
  of `σ(Φ)` extends to a model of `Φ` by setting `S^{I'} := (R^{I'})⁻¹`, and
  every model of `Φ` is already a model of `σ(Φ)`. Since roles are not part of
  the published taxonomy, `Φ ⊨ A ⊑ B` iff `σ(Φ) ⊨ A ⊑ B` for concept names.

Test `reciprocal_bridge_rewrite_is_conservative_when_the_dropped_role_is_idle`
runs the case where the dropped role occurs only in the bridges, so the
rewritten set is pure EL, and pins that the two taxonomies are equal.

For a **one-way** bridge only `R⁻ ⊑ S` holds. `S` may be strictly larger than
`R⁻` in a model, so `σ` is not truth-preserving and the rewrite is not
available. Test `a_one_way_bridge_is_not_a_role_definition` shows the converse
is not free: a reflexive `S` plus the one-way bridge publishes a taxonomy, and
adding the converse forces a reflexive `R`, breaks the base model against the
residual, and leaves the route with nothing to publish.

## Why the rewrite does not remove the work

`σ` maps EL normal forms to reverse-oriented forms:

| before | after | shape |
| --- | --- | --- |
| `∃S.C ⊑ D`, i.e. `S(x,y) ∧ C(y) → D(x)` | `R(y,x) ∧ C(y) → D(x)` | head on the role TARGET |
| `A ⊑ ∃S.B`, i.e. `A(x) → S(x,f(x))` | `A(x) → R(f(x),x)` | existential on the role SOURCE |
| `S ⊑ T` | `R⁻ ⊑ T` | not NF6 |
| `T ⊑ S` | `T ⊑ R⁻` | not NF6 |
| `R₁∘S ⊑ T` | mixed-orientation chain | not NF7 |
| `Reflexive(S)` | `Reflexive(R)` | stays NF, and is sound |

`to_nf` refuses the first two wirings by name, and the refusal is deliberate:
"a head on the target or a self-loop body is NOT `∃R.A ⊑ B`", reading it so
being unsound. Test `the_canonicalised_reverse_forms_are_outside_to_nf` pins that
both rewritten shapes screen as non-EL and that `classify_inner` returns `None`
on them.

So the rewrite deletes 12 clauses on 1194 and creates 55,721 rules in two
normal forms the completion does not have. That accounts for the reported
measurement (150 s wall and about 14 GB before base completion, against 96.19 s
and 3.29 GiB for the retained ordinary EL base) without any appeal to duplicate
reverse edges.

## Why reverse rules cannot run on this node space

`elcomplete.rs` uses one node per concept name. `init_state` and NF3 give the
edge `(c, r, filler)` where `filler` is the filler **concept id**, and
`sub_super[c]` is at once the label of `c`'s canonical element and the published
super-set of the named class `c`. In pure EL those coincide, which is why the
completion is correct and small.

With a reverse rule they do not coincide. The node for `B` is the `R`-successor
of every context `A` with `A ⊑ ∃R.B`. Firing `∃R⁻.C ⊑ D` there from one
`C`-labelled predecessor writes `D` into `sub_super[B]`, which is the assertion
`B ⊑ D`. That claims every `B`-instance has a `C`-labelled `R`-predecessor,
which nothing entails: a `B`-instance need have no `R`-predecessor at all.

The counter-model in
`a_reverse_rule_at_a_shared_witness_would_assert_a_named_subsumption`:

```
A ⊑ ∃R.B   A1 ⊑ A   A2 ⊑ A   A1 ⊑ C   ∃S.C ⊑ D   ∃R.D ⊑ E   S ≡ R⁻

a1: A1,A,C   b_1: B,D   R(a1,b_1)   S(b_1,a1)
a2: A2,A     b_2: B     R(a2,b_2)   S(b_2,a2)
```

`A1 ⊑ E` is entailed. `A2 ⊑ E` is not: `b_2` has no `C`-labelled `S`-successor.
The shared-witness reverse firing writes `D` at the node for `B`, and the test
shows that the same ontology with `B ⊑ D` added as an axiom does derive
`A2 ⊑ E`. The reverse firing and the axiom are the same operation.

The sharing that does this is **inheritance** sharing, not repeated axioms, and
that distinction decides how common the defect is. On 1194 only 8 of the 130,268
distinct `(role, filler)` witness nodes carry more than one existential axiom,
so at the axiom level witnesses look almost private. They are not. The node for
`B` collects an in-edge from every context whose label contains the axiom
subject, and counting only asserted unit subsumptions (a lower bound: NF2 and
NF4 add more) gives, per witness node of a bridged role:

| role | witness nodes | min | median | p90 | max |
| --- | --- | --- | --- | --- | --- |
| `BFO_0000050` | 28,826 | 3 | 5 | 26 | 5,533 |
| `RO_0002202` | 28,826 | 3 | 5 | 25 | 9,456 |
| `BFO_0000051` | 10,256 | 3 | 4 | 44 | 2,917 |
| `RO_0002203` | 102 | 2 | 3 | 5 | 13 |
| `surrounded_by__uberon` | 32 | 2 | 4 | 14 | 230 |
| `proximally_connected_to` | 56 | 2 | 3 | 9 | 41 |

400-node samples per role, seed 20260802,
`role_census.py --witness-sharing 400`. The minimum over every bridged role is
2, so **not one witness node in 1194 is private**. A reverse rule has no node it
can fire at without a guard over at least 2, and typically 5, contexts.

Reverse NF3 has the same defect. `A ⊑ ∃R⁻.B` at context `A` wants the edge
`(node_B, R, node_A)`, giving the shared node `B` an out-edge to a named class,
after which every forward NF4 on `R` fires at `node_B` from `A`'s labels and
writes into the class `B`.

This is why the certificate is right to fail closed and why the failure is not
a tuning problem. The closed structure remains a model, so it bounds the
taxonomy from above; the base facts are entailed, so they bound it from below;
when the bounds differ there is nothing to publish. `KM_ELC_CERT=3` reported
exactly one such gap on 1194 (`mirrored edge would add concept 359875 at node
236226`, virtual role `BFO_0000050`), and `BFO_0000050` carries 144,130 NF4
consumers, so the gap is bulk, not an edge case.

## Lazy and symbolic alternatives

| alternative | verdict |
| --- | --- |
| **Virtual mirror index** (`codex/opus-1194-bridge`, uncommitted): `heads[R]`/`bases[S]` role index, each edge-consuming rule fires a second transposed time off `in_edges`, no mirror edge stored | Correct and the best available shape. Stores nothing, but still derives the full inverse label closure, which is the actual cost. Does not close 1194 (see the 2026-08-01 relevance-certificate run above). Its chain gate reads `idx.nf7_by_pair`, which is empty on 1194 (see the census), so it does not cover the marker-compiled chains. |
| **Demand-driven / goal-directed mirror**: expand a transposed edge only when a residual clause queries it | The certificate already probes with `edge_holds`, which answers a transposed query by one hash lookup on the other endpoint. That part is already lazy. It does not avoid the closure, because the closure is what decides inertness. |
| **Symbolic role terms** (carry `R⁻` as a first-class role literal instead of a second role id) | This is exactly the canonicalisation under a different name. It removes the second role id and produces the same reverse-oriented rules, with the same node-space problem. |
| **Relevance fence over named-class reachability** | Cannot exist on this node space: every node is a named class, so every inverse consequence is a named-class consequence by construction. The measured reachability (64,222 to 70,231 of 70,231) confirms it but understates the reason. |
| **Inertness proof only** (do not publish the closure, only use it to certify the base) | Sound and already implemented. Fails closed on 1194 because the mirror really does change named labels. |

## Fail-closed gates

If canonicalisation is implemented anyway, these are the conditions. Each must
refuse the ontology (return `None` from `classify_inner`, or leave the bridges
in the residual) rather than proceed.

**G1 Reciprocity.** Canonicalise only a pair with both swapped inclusions
present, matched structurally: one role atom in body and head, four plain
variables, `body.source == head.target`, `body.target == head.source`,
`body.source != body.target`. A one-way bridge is not a definition (G7).

**G2 Totality before deletion.** The bridge clauses may be deleted only once
the dropped role occurs nowhere else. Enumerate every occurrence: clause role
atoms in body and head, residual clauses, `CardMeta.role`, `DefinerMeta.role`,
`SourceAxiomMeta` concept trees, reflexive facts, ground role assertions, and
the `named` / `declared` / `el_rbox_safe` meta. Any occurrence the rewriter does
not recognise means the bridges stay. Partial rewriting without deletion is
always sound and needs no gate, but it is also pointless.

**G3 Role inclusions.** `S ⊑ T` becomes `R⁻ ⊑ T` and `T ⊑ S` becomes `T ⊑ R⁻`;
neither is NF6. The gate is a fixpoint over role **literals**, not a per-pair
check: close `{R ⊑ S}` and `{R⁻ ⊑ S}` under both polarities
(`R ⊑ S` gives `R⁻ ⊑ S⁻`, `R⁻ ⊑ S` gives `R ⊑ S⁻`), split the result into
forward inclusions, which are entailed NF6 and may be added, and residual
`R⁻ ⊑ T` pairs, which need reverse support or a refusal.
`close_bridged_rbox` in the `codex/opus-1194-bridge` prototype computes this.
On 1194 it is live: `BFO_0000050` has 10 sub-roles and `UBREL_0000002 ⊑
BFO_0000051` transposes 28,826 existential axioms into `BFO_0000050`.

**G4 Chains, including compiled ones.** Refuse any NF7 whose `r1`, `r2` or `sup`
carries transposed edges. This is necessary but **not sufficient**: the frontend
compiles `Trans(R)` and `R∘S ⊑ T` into `__trans__` / `__chain__` NF4 marker
clauses, and on 1194 NF7 is empty while 272,040 `__trans__` and 143,999
`__chain__` atoms are present. Marker clauses are ordinary NF4 and are covered
by whatever NF4 treatment is chosen, so the gate must be documented as an NF7
gate and not as a chain gate.

**G5 Reflexivity.** `Reflexive(S)` rewrites to `Reflexive(R)`, which is sound
and cheap. Recompute `reflexive_roles`, `build_idx`'s `reflexive_closed`, and
`seed_reflexive_edges` **after** the substitution, because the role hierarchy it
closes over has changed (G3). `Irreflexive(S)` is `S(x,x) → ⊥`, a residual
clause, and falls under G6.

**G6 Cardinality and residual atoms.** Rewrite every residual role atom on the
dropped role and re-`compile_residual`. Ranges `∃S⁻.⊤ ⊑ D` become
`∃R.⊤ ⊑ D`, which is a domain axiom and moves **into** EL; that is a gain.
Cardinality clauses over `S` become cardinality over `R` in the opposite
direction, which the checker can answer only if it can enumerate `R`-predecessors,
so refuse unless `in_edges` is maintained for that role at check time. Refuse
outright if `CardMeta` or `DefinerMeta` mentions the dropped role and the side
channel is not rewritten with it. On 1194 all of G6 is vacuous: no bridged role
has any residual occurrence.

**G7 One-way bridges.** Leave them in the residual. A one-way bridge may be read
as a definition only if the head role has no deriving occurrence anywhere
(`nf3`, `nf6_sup`, `nf7_sup`, `reflexive`, `bridge_head`, `residual_head`,
ground assertion) and the clause set is Horn, so that the least model gives the
role exactly the transpose. This is a narrow case and it is not the case on
1194: `distal_part_of` and `proximal_part_of` each have a `bridge_head`
occurrence.

There is a cheaper and more useful observation for one-way bridges. If the
**body** role has no deriving occurrence, its extension is empty in the
canonical model and the clause is satisfied with no mirror at all. Both of
1194's one-way bridges have this shape (`has_distal_part` and
`has_proximal_part` occur only as `bridge_base`), so both are free. Test
`a_bridge_whose_body_role_is_never_derived_is_discharged_by_the_base_model`
pins it. Note that this still leaves the 6 reciprocal pairs, so canonicalising
every reciprocal pair does **not** make 1194 pure EL by itself; it makes it
reverse-EL, which is a different and harder fragment.

**G8 Pipeline position.** Canonicalise inside `to_nf` / `elc`, never in the
frontend. `preprocess.rs::transitivity_clauses` builds its markers by scanning
forward-oriented NF4 clauses; if the substitution ran before it, it would see
reverse-oriented bodies it does not match and would silently emit fewer markers.

**G9 Incremental sessions.** `IncrementalElClassifier` keys retained facts on
`NormalFormKey`. A substitution rewrites keys wholesale, so any change to the
bridge set must force a full restart, in the same way the Skolem-half rewrite
already does.

## What would have to change

Reverse rules need a node space where a witness is distinguishable from its
filler class. The minimum sound design is two changes together:

1. **Split the node space.** Give each existential its own witness node,
   distinct from the filler concept's class node, carrying the filler's label
   plus locally derived facts. Reverse-derived facts then stay internal instead
   of landing in the taxonomy.
2. **Universal-predecessor guard.** A witness is still shared by every
   predecessor context, so firing `∃R⁻.C ⊑ D` at witness `w` is sound only when
   **every** stored in-edge of `w` over `R` or a sub-role has `C` in its source
   label. Otherwise refuse, or split `w` per predecessor, which is the ELI
   unravelling and is where the exponential lives.

The witness-sharing table above already prices this. Every witness node of every
bridged role in 1194 has at least 2 predecessor contexts and typically 5, by a
lower-bound count that ignores NF2 and NF4 label growth, so the guard never gets
the easy case of a private witness. The measurement that would settle it is to
run the guard over the **base** saturated model, with no closure, and count how
many `(witness, reverse rule)` pairs pass. If the pass rate is near zero, which
the table predicts, the design collapses to fail-closed and `elc` cannot reach
1194 by this route at all.

The alternative is to stop extending `elc` and give the CB engine a Horn-ELI
configuration. 1194's EL part is Horn, contexts in `engine.rs` are exactly the
per-root structure the guard above is trying to approximate, and the calculus is
already certified.

## Implementation and test checklist

Only if the decision is to build it anyway.

- [ ] `take_inverse_bridges`-style structural extraction with the G1 wiring test,
      and a test that a forward inclusion and a self-loop inclusion do not match.
- [ ] Occurrence enumeration for the dropped role across clauses, residual,
      `CardMeta`, `DefinerMeta`, `SourceAxiomMeta`, reflexive facts, ground
      assertions and meta (G2), with a test per side channel that an
      unrewritten occurrence refuses.
- [ ] Role-literal closure (G3) with tests for: an entailed forward inclusion
      recovered through an inverse detour, a sub-role landing under the opposite
      half, and a residual `R⁻ ⊑ T` that refuses.
- [ ] Orientation choice recorded in the debug output; a test that both
      orientations of the same pair give the same taxonomy.
- [ ] NF7 gate (G4) plus an explicit test that a `__trans__`-compiled transitive
      bridged role does **not** trip it, so the limitation is documented in code.
- [ ] Reflexivity recomputed after substitution (G5), with a test where the
      role hierarchy changes the reflexive closure.
- [ ] Residual rewrite and `compile_residual` re-run (G6), with a range axiom
      test showing `∃S⁻.⊤ ⊑ D` becoming a domain axiom.
- [ ] One-way bridges refused (G7); keep
      `a_bridge_whose_body_role_is_never_derived_is_discharged_by_the_base_model`.
- [ ] Reverse NF3 and reverse NF4 evaluated on a split node space with the
      universal-predecessor guard, and a test that the guard refuses the
      `A / A2 / B` counter-model above rather than deriving `A2 ⊑ E`.
- [ ] Incremental restart on a bridge-set change (G9).
- [ ] Full release suite green, then the soundness-vs-gold table with no
      regression in unsound / incomplete / both-disagree.

## Reproducing the census

```bash
km ofn --meta /tmp/1194.meta ore_ont_1194.owl > /tmp/1194.clauses.json
python3 engine/py/role_census.py --residual-shapes --witness-sharing 400 \
    --json /tmp/1194.rolecensus.json /tmp/1194.clauses.json
```

The script is reasoner-free: it reads the clause JSON and classifies shapes, so
it runs anywhere and takes about 9 s and 2.4 GiB on the 270 MB 1194 capture.

## Tests added by this audit

In `engine/src/elcomplete.rs`:

- `reciprocal_bridge_rewrite_is_conservative_when_the_dropped_role_is_idle`
- `a_bridge_whose_body_role_is_never_derived_is_discharged_by_the_base_model`
- `a_reverse_rule_at_a_shared_witness_would_assert_a_named_subsumption`
- `a_one_way_bridge_is_not_a_role_definition`
- `the_canonicalised_reverse_forms_are_outside_to_nf`

They add no production behaviour. They pin the facts a canonicalising
implementation would have to respect, and the third one fails if anyone lands
reverse-oriented rules on the current node space.
