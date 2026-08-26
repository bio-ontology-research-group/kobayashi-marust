#!/bin/bash
#SBATCH --job-name=km-flat-source-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/source-shapes-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections, json, os

ids = [868, 8486, 9674, 10689, 8737, 16744, 15059, 13482, 1559, 15280,
       14459, 10750, 1012, 14042, 16008]
root = "/ibex/scratch/hohndor/km/corpus"
for oid in ids:
    path = f"{root}/ore_ont_{oid}.owl"
    counts = collections.Counter()
    examples = {}
    with open(path, encoding="utf-8") as source:
        for raw in source:
            line = raw.strip()
            if not line:
                continue
            if line == ")":
                kind = "close"
            elif "(" in line:
                kind = line.split("(", 1)[0]
            else:
                kind = "other"
            counts[kind] += 1
            examples.setdefault(kind, line[:240])
    print(json.dumps({
        "ontology": oid,
        "bytes": os.path.getsize(path),
        "counts": dict(sorted(counts.items())),
        "examples": {k: examples[k] for k in sorted(examples)
                     if k not in {"Declaration", "Prefix", "SubClassOf"}},
    }, sort_keys=True))
print("SOURCE_SHAPE_AUDIT_COMPLETE")
PY
