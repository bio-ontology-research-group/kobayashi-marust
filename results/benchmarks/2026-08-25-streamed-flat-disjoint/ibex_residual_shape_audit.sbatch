#!/bin/bash
#SBATCH --job-name=km-residual-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=3G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-stream-flat-20260825/residual-shapes-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections, json, os

ids = [6233, 11395, 15803, 1559, 3524, 3836, 12528, 10073, 11315]
root = "/ibex/scratch/hohndor/km/corpus"

def outer_term(text):
    payload = text[len("SubClassOf("):-1]
    depth = 0
    for index, char in enumerate(payload):
        if char == "(": depth += 1
        elif char == ")": depth -= 1
        elif char.isspace() and depth == 0:
            left, right = payload[:index], payload[index:].strip()
            kind = lambda term: "named" if term.startswith("<") else term.split("(", 1)[0]
            return kind(left) + "->" + kind(right)
    return "malformed"

for oid in ids:
    path = f"{root}/ore_ont_{oid}.owl"
    top = collections.Counter()
    subclasses = collections.Counter()
    examples = {}
    with open(path, encoding="utf-8") as source:
        for raw in source:
            line = raw.strip()
            if not line: continue
            kind = "close" if line == ")" else line.split("(", 1)[0]
            top[kind] += 1
            if line.startswith("SubClassOf("):
                shape = outer_term(line)
                subclasses[shape] += 1
                examples.setdefault(shape, line[:360])
    print(json.dumps({"ontology": oid, "bytes": os.path.getsize(path),
        "top": dict(sorted(top.items())),
        "subclasses": dict(sorted(subclasses.items())),
        "examples": {key: examples[key] for key in sorted(examples)}}, sort_keys=True))
print("RESIDUAL_SHAPE_AUDIT_COMPLETE")
PY
