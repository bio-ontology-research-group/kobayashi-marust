## F inputs (499)

| outcome | inputs |
|---|---:|
| Lean accepts | 499 |
| Lean accepts, Rust agrees (names and counts) | 499 |
| Lean accepts, Rust disagrees | 0 |
| Lean accepts, Rust rejects or crashes | 0 |
| Lean rejects | 0 |

Rust registry flags on accepted F inputs: none

### Five largest F inputs

| input | MB | axioms | Lean wall s | Lean parse (stderr) | Lean max RSS MB | Rust wall s | Rust max RSS MB |
|---|---:|---:|---:|---|---:|---:|---:|
| ore_ont_15059.owl | 577 | 3280784 | 20.2 | read 3044 ms, parse 13013 ms | 2198 | 27.6 | 1667 |
| ore_ont_1559.owl | 394 | 2513931 | 17.3 | read 2431 ms, parse 9771 ms | 1550 | 14.2 | 1287 |
| ore_ont_15203.owl | 394 | 2513922 | 17.5 | read 2538 ms, parse 9869 ms | 1552 | 19.0 | 1288 |
| ore_ont_3836.owl | 350 | 1928386 | 10.7 | read 2029 ms, parse 7074 ms | 1340 | 8.0 | 1005 |
| ore_ont_3524.owl | 305 | 2097631 | 9.4 | read 2166 ms, parse 5778 ms | 1159 | 6.7 | 866 |

Lean wall time over all F inputs: 276 s; max 20.2 s

## Non-F inputs (1282)

Lean status: {'rejected': 1281, 'ok': 1}

| rejection reason | inputs |
|---|---:|
| out of fragment: ClassAssertion (ABox assertion) | 261 |
| out of fragment: ObjectMaxCardinality (cardinality restriction) | 175 |
| out of fragment: FunctionalObjectProperty (object property characteristic) | 134 |
| out of fragment: ObjectMinCardinality (cardinality restriction) | 122 |
| out of fragment: ObjectOneOf (nominal) | 112 |
| out of fragment: ObjectPropertyAssertion (ABox assertion) | 71 |
| out of fragment: ObjectHasValue (nominal) | 69 |
| out of fragment: ObjectExactCardinality (cardinality restriction) | 54 |
| out of fragment: DataHasValue (data construct) | 43 |
| out of fragment: DataPropertyDomain (data property axiom) | 42 |
| out of fragment: DataMinCardinality (data construct) | 33 |
| out of fragment: owl:topObjectProperty | 25 |
| out of fragment: DataSomeValuesFrom (data construct) | 21 |
| out of fragment: DataMaxCardinality (data construct) | 20 |
| out of fragment: FunctionalDataProperty (data property axiom) | 18 |
| out of fragment: DataPropertyAssertion (ABox assertion) | 13 |
| out of fragment: DataExactCardinality (data construct) | 11 |
| out of fragment: DataPropertyRange (data property axiom) | 11 |
| out of fragment: ReflexiveObjectProperty (object property characteristic) | 10 |
| out of fragment: DataAllValuesFrom (data construct) | 10 |
| out of fragment: SameIndividual (ABox assertion) | 7 |
| out of fragment: InverseFunctionalObjectProperty (object property characteristic) | 7 |
| out of fragment: ObjectHasSelf (self restriction) | 4 |
| out of fragment: DisjointUnion (disjoint union) | 3 |
| out of fragment: SubDataPropertyOf (data property axiom) | 3 |
| out of fragment: DLSafeRule (rule) | 1 |
| syntax error: unexpected @prefix before Ontology | 1 |

- non-F input with Lean status ok: /mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_7216.owl (None)

Rust status on non-F inputs: {'ok': 1282}
