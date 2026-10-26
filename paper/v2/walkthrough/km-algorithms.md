# KM v1.5.3: the three classification procedures and the automatic router

*2026-10-26T13:05:45Z by Showboat 0.6.1*
<!-- showboat-id: 8d814153-0f9e-46d8-9ac2-214dfd60a8b6 -->

This walkthrough accompanies the System section and the algorithm appendix of the KM paper. It runs the tagged release `v1.5.3` (commit `b5abf83a`) on small ontologies from the repository. For each procedure it shows the stages a classification passes through:

- the EL++ completion worker;
- the consequence-based (CB) context engine;
- the two hypertableau procedures: the native hypertableau, and the function-by-function Konclude port reached through the "bridge";
- the automatic router that chooses among them.

Every block below was executed with `showboat exec` in a checkout of `v1.5.3`, with the binary built by `cd engine && CARGO_TARGET_DIR=../target cargo build --release --bin km`. Run `showboat verify` with `--workdir` set to such a checkout to re-execute it. Wall-clock times are masked as `T` so that the recorded output is reproducible.

```bash
git log -1 --format="%h %ad %s" --date=short; echo "$(target/release/km routes | wc -l) named routes"
```

```output
b5abf83a 2026-10-25 docs: add v1.5.3 release and matched classification benchmark protocol
42 named routes
```

## 1. The automatic router

`km classify` sets `KM_ROUTE=auto`. Routing has four layers:

1. Source rewrites before the frontend: data and rule source reduction, symbolic cardinalities, ABox quotients, flat `SubClassOf` taxonomies, and the negative-existential mirror.
2. `routing::select` on the streaming source profile. It applies an ordered list of typed predicates and a six-class semantic fragment gate.
3. Refinements after normalisation: ABox elision, EL promotion or withdrawal, and the typed-ABox SHOIQ specialist.
4. Bounded conductor probes and per-profile schedule overrides before the selected bundle runs.

At v1.5.3 the leaf `routing_tree_generated::select` is a constant that returns `production_all`. Every other decision is a hand-written predicate in `engine/src/routing.rs`.

~~~mermaid
flowchart TD
  A[km classify, KM_ROUTE=auto] --> B[validate input, canonicalise built-ins]
  B --> C{source rewrites: data/rule reduction, symbolic cardinality, ABox quotient, flat NF1, mirror}
  C -- certified answer --> Z[publish]
  C -- declined --> D[frontend: streaming parse, source profile, Konclude expressivity code]
  D --> E{R1-R8 typed source predicates}
  E -- match --> E1[nominals / production_all / certified_el_production / ht_bridge]
  E -- none --> F{semantic fragment gate}
  F -- rules --> G[ht_rules]
  F -- native bridge ABox --> H[certified_nominals]
  F -- other ABox or nominal --> I{N1-N12 ABox predicates}
  I --> I1[certified_nominals / elc / production_all / certified_card_* / nominals]
  F -- certified positive ABox or nominal-free core --> J{C1-C7 EL, Horn, near-EL, bounded CB}
  J -- match --> J1[elc / certified_el_production / cb_absorb8 / cb_plain1 / cb_trigger16 / production_all]
  J -- none --> K[constant leaf: production_all or production_all1]
  E1 & G & H & I1 & J1 & K --> L{post-normalisation: ABox elision, EL promotion or withdrawal, NI-ABox refinement}
  L --> M{bounded probes: bridge-first 8 s or 12 s, compact typed bridge, production with EL-ABox check}
  M -- answer --> Z
  M -- declined --> N[apply route bundle and schedule overrides]
  N --> O{mechanism}
  O -- atomic --> P[single worker: elc, ht bridge, or cb]
  O -- portfolio --> Q[in-process EL and CB fast paths, then CB vs HT race with certified EL]
  P -- defer, error, RSS trip --> R[exact fallback: production_all or nominals]
  R --> N
  P -- answer --> T[map to IRIs, ABox consistency checks]
  Q --> T
  T --> Z
~~~

`km profile` reports the route that `routing::select` returns for a source. This is layer 2 only.

```bash
KM=target/release/km
for f in engine/tests/fixtures/automatic_el_fallback.ofn examples/ontologies/trans_test.ofn examples/ontologies/kinship_chain.ofn examples/ontologies/forall_intro.ofn examples/ontologies/disjunction.ofn oracle/ontologies/card_ge_sub.ofn oracle/ontologies/nom_oiq_funct.ofn engine/tests/fixtures/rule_consistent.ofn; do
  printf "%-48s " "$f"
  $KM profile "$f" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d[\"selected_route\"], d[\"profile\"][\"expressivity\"][\"code\"])"
done
```

```output
engine/tests/fixtures/automatic_el_fallback.ofn  elc ALI+
examples/ontologies/trans_test.ofn               elc SI
examples/ontologies/kinship_chain.ofn            ht_bridge SRI
examples/ontologies/forall_intro.ofn             production_all SI
examples/ontologies/disjunction.ofn              certified_nominals SHI
oracle/ontologies/card_ge_sub.ofn                ht_bridge ALEIQ+
oracle/ontologies/nom_oiq_funct.ofn              nominals SOIF
engine/tests/fixtures/rule_consistent.ofn        ht_rules ALI+
```

`KM_TIMING=1` prints the dispatched route on standard error, together with any probe or fallback that answered. The JSON output of `km classify` has no route field, so the trace is the only record of the route. The rule ontology is answered by the ground-rule source reduction (layer 1) before the frontend routes it, which is why its trace reads `route=manual`. The two ontologies routed to `ht_bridge` by the bounded bridge-first probe answer within the probe.

```bash
KM=target/release/km
for f in engine/tests/fixtures/automatic_el_fallback.ofn examples/ontologies/trans_test.ofn examples/ontologies/kinship_chain.ofn examples/ontologies/forall_intro.ofn examples/ontologies/disjunction.ofn oracle/ontologies/card_ge_sub.ofn oracle/ontologies/nom_oiq_funct.ofn engine/tests/fixtures/rule_consistent.ofn; do
  echo "== $f"
  KM_TIMING=1 $KM classify "$f" 2>&1 >/dev/null | grep -E "route=|accepted|declined" | sed -E "s/@ [0-9.]+s/@ T/"
done
```

```output
== engine/tests/fixtures/automatic_el_fallback.ofn
KM_TIMING frontend done @ T route=elc
== examples/ontologies/trans_test.ofn
KM_TIMING frontend done @ T route=elc
== examples/ontologies/kinship_chain.ofn
KM_TIMING frontend done @ T route=ht_bridge
== examples/ontologies/forall_intro.ofn
KM_TIMING frontend done @ T route=production_all
== examples/ontologies/disjunction.ofn
KM_TIMING frontend done @ T route=ht_bridge
KM_TIMING bounded bridge-first accepted @ T
== oracle/ontologies/card_ge_sub.ofn
KM_TIMING frontend done @ T route=ht_bridge
== oracle/ontologies/nom_oiq_funct.ofn
KM_TIMING frontend done @ T route=ht_bridge
KM_TIMING bounded bridge-first accepted @ T
== engine/tests/fixtures/rule_consistent.ofn
KM_TIMING frontend done @ T route=manual
KM_TIMING automatic data source accepted: KM_GROUND_RULE_SOURCE
```

An atomic route that declines falls back to an exact route. The following run reproduces the repository test `engine/tests/elc_certificate.rs`. The EL worker is replaced by `/bin/false` and in-process EL is disabled, so the `elc` route fails. Under `auto`, the conductor reruns the ontology on `production_all` and still answers. Under the forced route `--route elc` it does not answer.

```bash
KM=target/release/km
KM_ELC_BIN=/bin/false KM_NO_INPROC_ELC=1 KM_TIMING=1 $KM classify engine/tests/fixtures/automatic_el_fallback.ofn 2>&1 | grep -E "declined|race:|^\{" | sed -E "s/[0-9]+\.[0-9]+s/T/g"
echo "--- forced elc route:"
KM_ELC_BIN=/bin/false KM_NO_INPROC_ELC=1 $KM classify --route elc engine/tests/fixtures/automatic_el_fallback.ofn >/dev/null 2>&1; echo "exit status $?"
```

```output
KM_TIMING atomic route elc declined @ T: worker elc exited 1: 
KM_TIMING race: HT worker spawned @ T after the CB stack started
KM_TIMING race: HT-first phase ended @ T (exited=true answer=true budget=0s)
{"consistent": true, "subsumptions": [[":A", ":B"]], "unsatisfiable": [], "dropped": 0}
--- forced elc route:
exit status 1
```

## 2. EL++ completion (`engine/src/elcomplete.rs`)

The EL worker proceeds in four steps:

1. `to_nf` maps every normalised DL clause to one of the normal forms NF1 to NF7: `A⊑B`, `A⊓B⊑C`, `A⊑∃R.B`, `∃R.A⊑B`, `A⊑⊥`, `R⊑S` and `R∘S⊑T`, plus reflexive roles. Every other clause is collected as a residual.
2. A cycle-free hierarchy consisting only of NF1 clauses is closed directly by a topological sort.
3. Otherwise the worker builds a packed per-concept rule index and saturates with the completion rules. The rules run over a context-local worklist with ELK's backward links and propagations.
4. A non-empty residual makes the worker decline (exit 3), unless a certificate mode is requested. The `Check` mode tests the residual clauses on the canonical model. The `Repair` mode intersects repaired models and hands undecided subjects to the CB engine.

~~~mermaid
flowchart TD
  A[normalised DL clauses] --> B[cert modes only: prune vacuous roles, orient inverse bridges]
  B --> C[to_nf: intern names, NF1-NF7 and reflexive roles, residual list]
  C -- filler without role half --> X[decline]
  C --> D{residual empty and NF1-only acyclic?}
  D -- yes --> D1[Kahn topological closure] --> R
  D -- no --> E{residual non-empty?}
  E -- yes, certificate off --> X
  E -- yes, certificate on --> F[compile residual with pinned Skolem witnesses]
  E -- no --> G
  F --> G[packed rule index, role closure, chain map; seed C⊑C, C⊑⊤, reflexive self-edges]
  G --> H[saturate: context worklist, backward links, propagations; serial, context-parallel or NF4 batch]
  H --> I{⊥ in label of ⊤?}
  I -- yes --> R[output full closure, unsatisfiable classes, consistency]
  I -- no --> J{residual?}
  J -- no --> R
  J -- yes --> K{Check: canonical model satisfies residual; Repair: model passes and intersection}
  K -- pass --> R
  K -- partial --> L[publish decided subjects; CB answers the residue]
  K -- fail --> X
~~~

The frontend turns an ontology into DL clauses. `km elc` consumes them. With `KM_ELC_PROFILE`, the worker counts the work items and rule scans.

```bash
KM=target/release/km; T=$(mktemp -d)
cat oracle/ontologies/chain_test.ofn | grep -vE "^\s*$"
$KM ofn oracle/ontologies/chain_test.ofn > $T/ch.json
echo "--- $(python3 -c "import json,sys; print(len(json.load(open(sys.argv[1]))[\"clauses\"]))" $T/ch.json) DL clauses; EL worker:"
KM_ELC_PROFILE=1 $KM elc < $T/ch.json 2>&1; echo; echo "exit status $?"; rm -r $T
```

```output
Prefix(:=<http://t#>)
Ontology(<http://t>
Declaration(Class(:A)) Declaration(Class(:Mid)) Declaration(Class(:C)) Declaration(Class(:D))
Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:S)) Declaration(ObjectProperty(:T))
SubObjectPropertyOf(ObjectPropertyChain(:R :S) :T)
SubClassOf(:A ObjectSomeValuesFrom(:R :Mid))
SubClassOf(:Mid ObjectSomeValuesFrom(:S :C))
SubClassOf(ObjectSomeValuesFrom(:T :C) :D)
)
--- 14 DL clauses; EL worker:
KM_ELC_PROFILE sub_items=26 edge_items=7 | nf1_scan=5 nf2_scan=0 nf2_label_side=0 nf3_scan=7 nf4_sub_scan=0 nf4_edge_scan=11 nf7_scan=0 botback=0 | nf4_batch_calls=0 nf4_batch_edges=0 nf4_batch_groups=0 nf4_batch_missing=0 | ctx_activations=9 link_items=0 par_workers=0 par_batches=0 par_messages=0
{"subsumptions":{"A":["D","Q_0","Q_2"],"Mid":["Q_1","__chain__S__C"],"Q_0":["D","Q_2"],"Q_1":["__chain__S__C"],"Q_2":["D"]},"inconsistent":false,"dropped":0}
exit status 0
```

The NF1-only fast path answers a flat hierarchy without saturation. The same input saturated by the general procedure gives the same taxonomy. With `KM_ELC_TIMING`, the fast path shows no `saturate` lap.

```bash
KM=target/release/km; T=$(mktemp -d)
printf "Prefix(:=<http://t#>)\nOntology(<http://t>\nSubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:A :D) SubClassOf(:D :C)\n)\n" > $T/flat.ofn
$KM ofn $T/flat.ofn > $T/flat.json
echo "fast path laps: $(KM_ELC_TIMING=1 $KM elc < $T/flat.json 2>&1 >/dev/null | grep -oE "KM_ELC_TIMING [a-z_+/()]+" | cut -d" " -f2 | tr "\n" " ")"
echo "general laps:   $(KM_ELC_TIMING=1 KM_ELC_NO_ACYCLIC_NF1=1 $KM elc < $T/flat.json 2>&1 >/dev/null | grep -oE "KM_ELC_TIMING [a-z_+/()]+" | cut -d" " -f2 | tr "\n" " ")"
canon(){ python3 -c "import json,sys; d=json.load(sys.stdin)[\"subsumptions\"]; print({k:sorted(v) for k,v in sorted(d.items())})"; }
a=$($KM elc < $T/flat.json 2>/dev/null | canon); b=$(KM_ELC_NO_ACYCLIC_NF1=1 $KM elc < $T/flat.json 2>/dev/null | canon)
echo "fast path: $a"; echo "general:   $b"; rm -r $T
```

```output
fast path laps: read parse to_nf classify serialise 
general laps:   read parse to_nf index+init/drop_clauses index+init/build_idx index+init/init_state index+init saturate certificate release output(strings) classify serialise 
fast path: {'A': ['B', 'C', 'D'], 'B': ['C'], 'D': ['C']}
general:   {'A': ['B', 'C', 'D'], 'B': ['C'], 'D': ['C']}
```

Context-parallel saturation partitions the contexts statically over workers and exchanges messages between them (`KM_ELC_PAR_CTX`). It must produce byte-identical output to the serial run. The router turns it on automatically only for large EL terminologies. Here it is forced on a small input to compare the two outputs.

```bash
KM=target/release/km; T=$(mktemp -d)
$KM ofn oracle/ontologies/trans_hier.ofn > $T/th.json
s=$($KM elc < $T/th.json 2>/dev/null | sha256sum | cut -c1-16)
p=$(KM_ELC_PAR_CTX=4 $KM elc < $T/th.json 2>/dev/null | sha256sum | cut -c1-16)
echo "serial   $s"; echo "parallel $p"
KM_ELC_PROFILE=1 KM_ELC_PAR_CTX=4 $KM elc < $T/th.json 2>&1 >/dev/null | grep -oE "par_workers=[0-9]+"; rm -r $T
```

```output
serial   6565b6584354dbfe
parallel 6565b6584354dbfe
par_workers=4
```

A non-EL clause is handled according to the certificate mode. With the certificate off, which is the default on the `elc` route, the worker declines before saturation. `disjunction.ofn` contains `Q ⊑ Female ⊔ Male`. In `Repair` mode the worker either certifies an answer, publishes a partial answer (exit 4), or declines.

```bash
KM=target/release/km; T=$(mktemp -d)
$KM ofn examples/ontologies/disjunction.ofn > $T/dis.json
KM_ELC_DEBUG=1 $KM elc < $T/dis.json 2>&1 >/dev/null | grep -oE "KM_ELC defer: [0-9]+ non-EL residual clause\(s\)"; echo "certificate off: exit $( $KM elc < $T/dis.json >/dev/null 2>&1; echo $?)"
echo "certificate repair: exit $(KM_ELC_CERT=2 $KM elc < $T/dis.json >/dev/null 2>&1; echo $?)"; rm -r $T
```

```output
KM_ELC defer: 4 non-EL residual clause(s)
certificate off: exit 3
certificate repair: exit 0
```

## 3. The consequence-based context engine (`engine/src/engine.rs`, `calc.rs`, `reasoner.rs`)

The CB worker works in five steps:

1. Interning: it interns the DL clauses into an ordered term representation and drops (and counts) clauses with unsupported terms. Clauses with individuals are kept only in nominal mode.
2. Preparation: it prepares an immutable, shared ontology with its indexes and trigger bits.
3. Contexts: it creates one root context with core `{A(x)}` per named query.
4. Saturation: each context runs a given-clause loop that applies Core, Hyper, Eq, Ineq, Factor and Elim to maximal literals. Succ and Pred messages connect the contexts and are processed in batched rounds until no message is pending. Nominal mode adds a ground context and the r-Succ, r-Pred, Join and Nom rules.
5. Reading off the taxonomy: `A ⊑ B` holds when the root context of `A` contains the unit clause `⊤ → B(x)`, and `A` is unsatisfiable when that context contains the empty clause.

~~~mermaid
flowchart TD
  A[DL clauses] --> B[intern terms; drop unsupported terms and non-normal role bodies; count dropped]
  B --> C[prepare once: ground-equality quotient, indexes, trigger bits, nominal parameters]
  C --> D[ordering: Sequoia definer order iff a head disjunction contains a definer]
  D --> E[queries: named classes; collapse told-equivalent classes]
  E --> F{threads}
  F --> G[per-thread engines over the shared prepared ontology; work stealing]
  G --> H[ground context if individuals]
  H --> I[root context per query, core A of x; shared closure base; Core rule]
  I --> J[given-clause loop: pop, recheck forward subsumption]
  J --> K[rules on maximal literals: Hyper, Eq, Factor, local Pred, Join, Nom]
  K --> L[Elim: tautology, duplicate, forward and backward subsumption]
  L --> J
  J -- worklist empty --> M[propagate semi-naively: Succ triggers, r-Succ, Pred pushes]
  M --> N{messages pending, under cap?}
  N -- yes --> O[batch round: apply all, then saturate and propagate each touched context]
  O --> N
  N -- cap or nominal budget hit --> P[incomplete: exit 4, nothing published]
  N -- no --> Q[read off units in root contexts; empty clause gives unsat; top and ground context give consistency]
  Q --> S{parallel run over 18 GiB or 190 s?}
  S -- yes --> T[retry on one thread with the per-function strategy]
  S -- no --> U[publish]
~~~

`factor_test.ofn` asserts `A ⊑ ≥3 R.C` and `A ⊑ ≤2 R.C`, so the Factor and Eq rules must merge witnesses and find `A` unsatisfiable. `KM_STATS` reports the number of contexts and rule applications. The default central strategy keys successor contexts by their unit triggers. The per-function strategy (`KM_NO_CENTRAL`), which is the retry schedule, creates one context per Skolem function. Both strategies derive the same subsumptions with different numbers of contexts.

```bash
KM=target/release/km; T=$(mktemp -d)
grep -E "SubClassOf|Functional|Disjoint" oracle/ontologies/factor_test.ofn
$KM ofn oracle/ontologies/factor_test.ofn > $T/f.json
echo "--- central strategy:"; KM_THREADS=1 KM_STATS=1 $KM engine < $T/f.json 2>&1 | grep -E "contexts=|subsumptions"
echo "--- per-function strategy:"; KM_THREADS=1 KM_STATS=1 KM_NO_CENTRAL=1 $KM engine < $T/f.json 2>&1 | grep -E "contexts=|subsumptions"; rm -r $T
```

```output
SubClassOf(:A ObjectMinCardinality(3 :R :C))
SubClassOf(:A ObjectMaxCardinality(2 :R :C))
--- central strategy:
KM_STATS contexts=4 roots=3 succs=1 root_wo_total=5 succ_wo_total=2 top_wo=0 avg_root_wo=2
{"subsumptions":{"A":["owl:Nothing"],"Bad":["A","owl:Nothing"],"C":[]},"derived_clauses":[],"inconsistent":false,"dropped":0}
--- per-function strategy:
KM_STATS contexts=6 roots=3 succs=3 root_wo_total=5 succ_wo_total=6 top_wo=0 avg_root_wo=2
{"subsumptions":{"A":["owl:Nothing"],"Bad":["A","owl:Nothing"],"C":[]},"derived_clauses":[],"inconsistent":false,"dropped":0}
```

Outside nominal mode, individual terms never reach the engine. The engine drops and counts any clause that mentions one. The singleton reading of a nominal is therefore lost, which is why the router never sends an ABox or nominal source without a separation certificate to the plain engine. In `nom_oiq_funct.ofn` the plain run misses `A ⊑ C`. With `KM_NOMINALS=1` the frontend keeps the individuals, and the engine runs the nominal calculus with a ground context and derives the subsumption.

```bash
KM=target/release/km; T=$(mktemp -d)
$KM ofn oracle/ontologies/nom_oiq_funct.ofn > $T/n0.json
$KM engine < $T/n0.json 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print(\"plain engine:   A has supers %s\" % sorted(d[\"subsumptions\"][\"A\"]))"
KM_NOMINALS=1 $KM ofn oracle/ontologies/nom_oiq_funct.ofn > $T/n1.json
KM_NOMINALS=1 KM_THREADS=1 $KM engine < $T/n1.json 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print(\"nominal engine: A has supers %s\" % sorted(d[\"subsumptions\"][\"A\"]))"; rm -r $T
```

```output
plain engine:   A has supers ['Q_0', 'Q_1', 'Q_2']
nominal engine: A has supers ['C', 'Q_0', 'Q_1', 'Q_2', 'Q_4']
```

Hitting a resource backstop marks the run incomplete, and the worker publishes nothing. Here the message cap is set to one message.

```bash
KM=target/release/km; T=$(mktemp -d)
$KM ofn oracle/ontologies/inv_test.ofn > $T/inv.json
KM_THREADS=1 KM_MSG_CAP=1 $KM engine < $T/inv.json > $T/out.json 2>$T/err.txt; echo "exit status $?"; grep -ioE "declined|cap[^,]*" $T/err.txt | head -2; rm -r $T
```

```output
exit status 4
cap; classification may be incomplete (truncated). 3 pending messages dropped.
declined
```

## 4. Hypertableau procedures

Both hypertableau procedures read the output of a converter, `orchestrate/cb_to_ht.rs`. Its only logical transformation is reverse Skolemisation. It also emits role-hierarchy clauses, transitivity propagation, first-class cardinality definitions and fences, and it counts every clause it cannot carry.

### 4.1 Native hypertableau (`engine/src/hypertableau.rs`)

The native procedure classifies in two phases:

1. A satisfiability test for each concept `A`. The root label of the model it finds gives the candidate subsumers. A node of an earlier model that already carries `A` can witness `A` instead.
2. A test of `A ⊓ ¬B` for each remaining candidate `B`. Every satisfiable test is a new model of `A`, and it prunes the remaining candidates.

Told subsumers are accepted without a test. Each test runs a depth-first search with delta-driven hyperresolution, dependency sets, backjumping, semantic branching and anywhere subset blocking.

~~~mermaid
flowchart TD
  A[HT clauses from cb_to_ht] --> B[index: trigger tables, global clauses, chains, cardinality definitions, nominals]
  B --> C[global consistency test]
  C -- inconsistent --> OUT[taxonomy, transitively closed]
  C -- consistent --> D[phase 1 per concept A: satisfiability test, or witness reuse]
  D --> E[dfs: delta hyperresolution, clash on assertion]
  E --> F[nominal merges; existential and at-least expansion on unblocked nodes]
  F --> G{disjunction scan}
  G -- unit --> E
  G -- branch --> H[order disjuncts; assert with branch level; recurse]
  H -- clash without this level --> I[backjump]
  H -- clash with this level --> J[assert negation of the tried disjunct; next disjunct]
  J --> E
  G -- complete --> K[at-most choose and merge; recognition]
  K --> L[A satisfiable: root label gives candidates]
  L --> M[accept told subsumers]
  M --> N[phase 2: test A and not B; satisfiable models prune candidates]
  N --> OUT
~~~

On the automatic route the native procedure runs only inside certificate-gated or CB-guarded arms. The cardinality arm `ht_card` is forced here so that its counters are visible. `card_ge_sub.ofn` derives `A ⊑ B` from `A ⊑ ≥2 R.C` and `B ≡ ≥1 R.C`.

```bash
KM=target/release/km
KM_HT_STATS=1 $KM classify --route ht_card oracle/ontologies/card_ge_sub.ofn 2>&1 | grep -E "classify-p1|witreuse|classify-p2|^\{" | sed -E "s/ dt_ms=[0-9]+ block_ms=[0-9]+ prop_ms=[0-9]+ expand_ms=[0-9]+//"
```

```output
KM_HT [classify-p1] qi=0/3 concept=0 sat=true nodes_last=3 branch_pushes=0 disjunct_tries=0 backtracks=0 backjumps=0 negfired=0 steps=2
KM_HT [witreuse] queries=3 reused=2 built=1
KM_HT [classify-p2] modelprune=true sat_q=3 phase2_tests=2
{"consistent": true, "subsumptions": [[":A", ":B"]], "unsatisfiable": [], "dropped": 0}
```

### 4.2 The Konclude port, reached through the bridge (`engine/src/konclude_ht/`)

The bridge builds Konclude's concept structures from the source axioms. It applies lazy unfolding and binary and partial triggered absorption, then common-disjunct extraction and role-chain automata. It then runs Konclude's approximation saturation, which answers every subject whose saturation node is clashed (unsatisfiable) or complete and sufficient (satisfiable, with an exact subsumer row). The remaining subjects go through the known/possible-subsumer (KPSet) classifier:

- a completion probe per subject, whose deterministic labels are read off;
- global pruning of the possible subsumers;
- verification of each remaining candidate, either by a deterministic subsumer, by refutation through a countermodel, or by a probe of `s ⊓ ¬c`.

Any clause the encoder cannot express, and any subject left undecided, makes the whole classification defer.

~~~mermaid
flowchart TD
  A[HT input and source axioms] --> B{input guards: inverse mirror, datatype, top role, nominal metadata}
  B -- fail --> X[defer]
  B -- pass --> C[build concept structures: lazy unfolding, binary and partial absorption]
  C --> D[preprocess: common disjuncts, role-chain automata, branch triggers]
  D --> E{unsupported clauses?}
  E -- yes --> X
  E -- no --> F{ABox or nominals?}
  F -- yes --> G[ABox consistency completion]
  G -- undecided --> X
  G -- inconsistent --> OUT
  F -- no --> H[seed known pairs from told and definition closure]
  G -- consistent --> H
  H --> I[approximation saturation within budget]
  I --> J[answer clashed and sufficient subjects]
  J --> K[phase 1: completion probe per residue subject, copy-on-write state]
  K --> L{probe}
  L -- budget stop or poisoned --> X
  L -- no OR branch --> M[deterministic read-off]
  L -- branched --> N[deterministic and possible subsumers; absences refute]
  M --> O[barrier; prune possible subsumptions]
  N --> O
  O --> P[phase 2: deterministic accept, countermodel refutation, else probe s and not c]
  P -- undecided --> X
  P -- all decided --> OUT[complete taxonomy and consistency]
~~~

`kinship.ofn` shows each stage on the `ht_bridge` route: the source encoding with absorption, the saturation pre-pass, and the KPSet phases. The second command counts the candidate pairs accepted as deterministic subsumers without a probe.

```bash
KM=target/release/km
KM_BRIDGE_PROGRESS=1 KM_BRIDGE_PHASE_TIMING=1 KM_HT_STATS=1 $KM classify --route ht_bridge examples/ontologies/kinship.ofn 2>&1 >/dev/null | grep -E "^bridge \[source-tbox\]|^BRIDGE-SATURATION:|^BRIDGE-SAT-PHASE prepare-total" | sed -E "s/[0-9]+\.[0-9]+s/T/g"
echo "deterministic-subsumer skips: $(KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 $KM classify --route ht_bridge examples/ontologies/kinship.ofn 2>&1 >/dev/null | grep -c "deterministic-subsumer")"
echo "--- same ontology with the deterministic-subsumer shortcut disabled; taxonomy identical:"
a=$($KM classify --route ht_bridge examples/ontologies/kinship.ofn 2>/dev/null | sha256sum | cut -c1-16)
b=$(KM_HT_NO_DET_SUBSUMER=1 $KM classify --route ht_bridge examples/ontologies/kinship.ofn 2>/dev/null | sha256sum | cut -c1-16)
echo "default $a"; echo "no-shortcut $b"
```

```output
bridge [source-tbox] axioms=11 eq=4/5 ["Mother", "Father", "Grandparent", "Narcissist", "Queen"] direct=8 role-links=0 absorbed-gci=2 top-gci=0 unsupported=0
BRIDGE-SAT-PHASE prepare-total: T (12 subjects)
deterministic-subsumer skips: 8
--- same ontology with the deterministic-subsumer shortcut disabled; taxonomy identical:
default 4cb6b37dee5132e7
no-shortcut 4cb6b37dee5132e7
```

### 4.3 The production portfolio

On `production_all` the supervisor starts the absorbed CB engine and one hypertableau worker restricted to certified arms, which are the bridge or the cardinality arm. A bridge-exclusive worker first runs alone, for up to 180 s, in the "HT-first" phase, and its answer is accepted at once. A CB answer is preferred whenever it arrives. Any other HT arm is accepted only after the CB engine fails or exceeds its budget. `forall_intro.ofn` follows this path: the bridge answers during the HT-first phase.

```bash
KM=target/release/km
KM_TIMING=1 $KM classify examples/ontologies/forall_intro.ofn 2>&1 | grep -E "route=|race:|^\{" | sed -E "s/[0-9]+\.[0-9]+s/T/g"
```

```output
KM_TIMING frontend done @ T route=production_all
KM_TIMING race: HT worker spawned @ T after the CB stack started
KM_TIMING race: HT-first phase ended @ T (exited=true answer=true budget=0s)
{"consistent": true, "subsumptions": [[":A", ":B"]], "unsatisfiable": [], "dropped": 0}
```

## 5. Scope of this walkthrough

The examples are deliberately small. Each one exercises one stage of one procedure on the tagged binary. The optimisation inventories, with their source locations, defaults and published origins, and the complete routing decision list are in the appendix of the paper. The benchmark evidence is in the release documents.

