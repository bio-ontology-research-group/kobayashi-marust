#!/bin/bash
#SBATCH --job-name=km-subclass-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/subclass-shapes-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections
import json
import re

ids = [15059, 8737, 16744, 1559, 14042]
root = "/ibex/scratch/hohndor/km/corpus"
named = re.compile(r"^SubClassOf\(<[^<>\s]+> <[^<>\s]+>\)$")

def outer_term(text):
    payload = text[len("SubClassOf("):-1]
    depth = 0
    split = None
    for i, ch in enumerate(payload):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch.isspace() and depth == 0:
            split = i
            break
    if split is None:
        return "malformed"
    left = payload[:split]
    right = payload[split:].strip()
    def kind(term):
        if term.startswith("<"):
            return "named"
        return term.split("(", 1)[0]
    return kind(left) + "->" + kind(right)

for oid in ids:
    counts = collections.Counter()
    examples = {}
    with open(f"{root}/ore_ont_{oid}.owl", encoding="utf-8") as source:
        for raw in source:
            line = raw.strip()
            if not line.startswith("SubClassOf("):
                continue
            shape = "named->named" if named.match(line) else outer_term(line)
            counts[shape] += 1
            examples.setdefault(shape, line[:500])
    print(json.dumps({
        "ontology": oid,
        "counts": dict(sorted(counts.items())),
        "examples": {key: examples[key] for key in sorted(examples)},
    }, sort_keys=True))
print("SUBCLASS_SHAPE_AUDIT_COMPLETE")
PY
