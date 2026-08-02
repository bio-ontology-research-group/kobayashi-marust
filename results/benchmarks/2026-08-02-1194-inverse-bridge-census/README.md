# ORE 1194 role-use census for the inverse-bridge audit

Reasoner-free structural census of the ORE 1194 clause set, produced for the
audit in [`../../../docs/INVERSE-BRIDGE-CANONICALISATION.md`](../../../docs/INVERSE-BRIDGE-CANONICALISATION.md).
No saturation runs here: the census classifies clause shapes with the same
branch structure as `elcomplete.rs::to_nf`, so a role's counters say exactly
which EL normal form each of its occurrences lands in.

## Input

`/tmp/1194.clauses.json`, the frontend output for `ore_ont_1194.owl`.
SHA-256 `5c0fdb40e5252e1d3092127bbe77c4cba74abf9da27041767f5c2959c2bc7da0`,
270,431,799 bytes, 1,062,240 clauses. The clause count matches the frontend
figure recorded in `2026-08-01-1194-query-scc/README.md`.

## Command

```bash
python3 engine/py/role_census.py --residual-shapes \
    --json ore_ont_1194.role_census.json /tmp/1194.clauses.json \
    > ore_ont_1194.role_census.txt
```

9.32 s wall, 2,467,452 KiB peak RSS on `leechuck-office`.

## Files

- `ore_ont_1194.role_census.txt` — the human summary.
- `ore_ont_1194.role_census.json` — per-role position counters, the reciprocal
  and one-way bridge split, the per-orientation gate table, and the residual
  shape histogram.

## Headline numbers

| quantity | value |
| --- | --- |
| clauses | 1,062,240 |
| distinct roles | 151 |
| NF4 `∃R.C ⊑ D` | 410,281 |
| NF1/NF2 | 391,047 |
| existential halves | 130,303 |
| residual clauses | 203 |
| NF6 role inclusions | 48 |
| domain axioms `∃R.⊤ ⊑ D` | 35 |
| inverse bridges | 14 |
| NF5 `A ⊑ ⊥` | 6 |
| **NF7 role chains** | **0** |
| `ind` / `aux` terms | 0 |

Bridges split into 6 reciprocal pairs (12 clauses) and 2 one-way bridges. Both
one-way body roles (`has_distal_part`, `has_proximal_part`) occur in no other
clause, so their extension is empty in the canonical model and both clauses are
satisfied with no mirror.

No bridged role has a residual, ground or chain occurrence, so the residual,
cardinality and chain gates are all vacuous on this ontology. Role chains and
transitivity are present but compiled into `__trans__` (272,040 atoms) and
`__chain__` (143,999 atoms) marker concepts, which are ordinary NF4, which is
why NF7 is empty.

Cheapest canonicalisation orientation across the six pairs turns 55,721 rules
reverse-oriented, of which 10,418 are reverse existentials. The worst
orientation turns 346,122. The spread does not translate into a cost difference:
the kept role carries `edges(R) ∪ transpose(edges(S))` either way, and the total
forward-plus-reverse rule count is the same in both directions.

## Witness sharing

130,303 existential axioms land on 130,268 distinct `(role, filler)` witness
nodes, and only **8** of those nodes carry more than one axiom (22 axioms in
total, at most 3 on one node). Witness nodes therefore look almost private at the
axiom level. They are not: the completion sends an edge to the node for `B` from
every context whose label contains the axiom subject.

`--witness-sharing 400` counts those contexts using asserted unit subsumption
only, which is a lower bound because NF2 and NF4 label growth adds more:

| role | witness nodes | min | median | p90 | max | mean |
| --- | --- | --- | --- | --- | --- | --- |
| `BFO_0000050` | 28,826 | 3 | 5 | 26 | 5,533 | 28.2 |
| `RO_0002202` | 28,826 | 3 | 5 | 25 | 9,456 | 40.4 |
| `BFO_0000051` | 10,256 | 3 | 4 | 44 | 2,917 | 43.2 |
| `RO_0002203` | 102 | 2 | 3 | 5 | 13 | 3.7 |
| `surrounded_by__uberon` | 32 | 2 | 4 | 14 | 230 | 13.5 |
| `surrounds` | 20 | 3 | 5 | 18 | 24 | 7.4 |
| `proximally_connected_to` | 56 | 2 | 3 | 9 | 41 | 5.1 |
| `distally_connected_to` | 37 | 2 | 4 | 9 | 41 | 5.5 |
| `BSPO_0000124` / `BSPO_0000125` | 1 each | 7 | 7 | 7 | 7 | 7.0 |
| `BSPO_0000098` | 4 | 3 | 6 | 8 | 8 | 5.0 |
| `BSPO_0000102` | 2 | 4 | 6 | 6 | 6 | 5.0 |

The minimum over every bridged role is 2, so not one witness node in this
ontology is private. Any privacy argument for reverse-oriented rules has to be
made after saturation, and starts from a worse position than this.

## Caveat

This capture has no individuals. The 221,086 class assertions recorded in
`docs/HARD-RESIDUAL-AUDIT.md` are not in it, so the ground-assertion gate is
untested by this census and needs a nominal capture before it is trusted.
