#!/bin/bash
#SBATCH --job-name=km-empty-source-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=3G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-source-audit-20260825/shapes-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections
import json
import os

ids = [6233, 5760, 7993, 2253, 14216, 5602, 9768, 4557, 2046, 9794, 4033]
root = "/ibex/scratch/hohndor/km/corpus"
for oid in ids:
    counts = collections.Counter()
    examples = {}
    path = f"{root}/ore_ont_{oid}.owl"
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
            if kind not in {"Prefix", "Declaration", "SubClassOf"}:
                examples.setdefault(kind, line[:600])
    print(json.dumps({
        "ontology": oid,
        "bytes": os.path.getsize(path),
        "counts": dict(sorted(counts.items())),
        "examples": {key: examples[key] for key in sorted(examples)},
    }, sort_keys=True))
print("EMPTY_SOURCE_SHAPE_AUDIT_COMPLETE")
PY
