#!/bin/bash
#SBATCH --job-name=km-htforce-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-historic-route-20260825/htforce-shapes-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections,json,os
ids=[10908,1016,11623,6934,10702,15672]
needles=["ObjectOneOf(","ObjectHasValue(","ObjectMinCardinality(",
 "ObjectMaxCardinality(","ObjectExactCardinality(","ObjectUnionOf(",
 "ObjectComplementOf(","ObjectAllValuesFrom(","ObjectInverseOf(",
 "owl:topObjectProperty","Data", "HasKey("]
root="/ibex/scratch/hohndor/km/corpus"
for oid in ids:
 path=f"{root}/ore_ont_{oid}.owl"; top=collections.Counter(); terms=collections.Counter()
 with open(path,encoding="utf-8") as source:
  for raw in source:
   line=raw.strip()
   if not line: continue
   top["close" if line==")" else line.split("(",1)[0]]+=1
   for needle in needles:
    if needle in line: terms[needle]+=line.count(needle)
 print(json.dumps({"ontology":oid,"bytes":os.path.getsize(path),
  "top":dict(sorted(top.items())),"terms":dict(sorted(terms.items()))},sort_keys=True))
print("HTFORCE_SHAPE_AUDIT_COMPLETE")
PY
