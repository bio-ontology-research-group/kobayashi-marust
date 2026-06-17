# Fixing HT incompleteness on pure-Horn ORE ontologies, verified against HermiT on the same ontology

*2026-06-17T08:03:38Z by Showboat 0.6.1*
<!-- showboat-id: 3998edc8-8bf8-40d5-9917-b799235e587d -->

The big HT version sweep flagged 8 routable ontologies as **incomplete** versus the Konclude gold signature, all of them pure Horn (no disjunction, no transitive roles): 5566, 6433, 6817, 8864, 8982, 12009, 14312, 15098. Hypertableau is trivially complete on Horn taxonomies, so this is a bug, not a fragment limit. Per the rule that you cannot meaningfully compare an incomplete algorithm, it must be fixed before any HermiT comparison.

Diagnosis: the incompleteness was identical under every blocking mode (subset / eq / core / ancestor) and under naive n-squared classification, so it is neither the blocking nor the model-based candidate pruning. The missing subsumptions all have a subsumee whose local name starts with Q_ (Q_minus, Q_plus, ...). These are REAL declared classes (Konclude keeps them in gold), but cb_to_ht.convert builds the tableau query set with an is_internal filter that drops any name starting with Q_/__/aux_/def_, with no escape for declared classes. So classify() never tested them.

The step below shows, for ore_ont_15098, how many DECLARED classes the old query filter wrongly drops.

```bash
ssh dragon "srun --account=pi-hohndor --partition=batch --time=10:00 --mem=12G --cpus-per-task=2 bash /ibex/scratch/hohndor/km/sb.sh bug 15098" 2>/dev/null | grep -vE 'Ibex|authoris|acceptab|permitted|ibex@|slack|^#|___|^[[:space:]]*$|srun:'

```

```output
ont 15098: declared (named) classes = 7133
declared classes the OLD query-filter WRONGLY drops = 13
examples: ['Q_minus', 'Q_minus0', 'Q_minus0_r', 'Q_minus_r', 'Q_plus', 'Q_plus0', 'Q_plus0_r', 'Q_plus_r']
'Q_minus' is a declared class: True
OLD filter calls 'Q_minus' internal: True  (=> excluded from queries = BUG)
```

Fix (engine/py/cb_to_ht.py): convert() now takes the frontend's `named` set and a declared class is ALWAYS a query, even if its local name looks internal: `queries = [cid(n) for n in con_names if (n in named_set or not is_internal(n)) and not is_bottom(n)]`. The HT engine, blocking, and pruning are unchanged. Below, the FIXED HT classifies all 8 formerly-incomplete onts; every one is byte-identical to the Konclude gold signature (incomplete=0, unsound=0).

```bash
ssh dragon "srun --account=pi-hohndor --partition=batch --time=12:00 --mem=10G --cpus-per-task=2 bash /ibex/scratch/hohndor/km/sb.sh fixed 15098 6817 12009 6433 14312 8864 5566 8982" 2>/dev/null | grep -vE 'Ibex|authoris|acceptab|permitted|ibex@|slack|^#|___|^[[:space:]]*$|srun:'

```

```output
ore_ont_15098  HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_6817   HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_12009  HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_6433   HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_14312  HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_8864   HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_5566   HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
ore_ont_8982   HT: status=ok  vs_Konclude_gold=MATCH  incomplete=0  unsound=0
```

Routing-consistency oracle: run HermiT (an independent hypertableau reasoner) on the SAME ore_ont_15098.owl, and confirm its classification signature is byte-identical to the Konclude gold. Same ontology in, same answer out across Konclude, HermiT, and the fixed KM HT, so the comparison is apples-to-apples.

```bash
ssh dragon "srun --account=pi-hohndor --partition=batch --time=10:00 --mem=8G --cpus-per-task=2 bash /ibex/scratch/hohndor/km/sb.sh hermit 15098" 2>/dev/null | grep -vE 'Ibex|authoris|acceptab|permitted|ibex@|slack|^#|___|^[[:space:]]*$|srun:'

```

```output
HermiT classified ore_ont_15098.owl (classes=211)
HermiT signature == Konclude gold signature: IDENTICAL (same ontology, same answer)
```

Conclusion: the HT engine, blocking, and pruning were never incomplete on these ontologies. The conversion simply never asked about declared classes whose local name looked internal (Q_minus, Q_plus, ...), so classify() skipped them. The one-line query-set fix (named escape in cb_to_ht.convert) restores completeness: all 8 formerly-incomplete onts are now byte-identical to Konclude gold, and HermiT independently agrees on the same ontology. The HT-vs-HermiT search-effort comparison is now meaningful and can proceed. NOTE: the production owl_classify HT path (convert called without named) carries the same latent gap and is being threaded with named for correctness.
