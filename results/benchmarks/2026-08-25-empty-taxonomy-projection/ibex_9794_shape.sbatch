#!/bin/bash
#SBATCH --job-name=km-9794-shape
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-source-audit-20260825/shape-9794-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections
import json
import re

path = "/ibex/scratch/hohndor/km/corpus/ore_ont_9794.owl"
counts = collections.Counter()
examples = {}
declarations = collections.Counter()
first_axiom = None
late_declarations = 0

def outer_term(line):
    payload = line[len("SubClassOf("):-1]
    depth = 0
    for index, char in enumerate(payload):
        if char == "(": depth += 1
        elif char == ")": depth -= 1
        elif char.isspace() and depth == 0:
            left, right = payload[:index], payload[index:].strip()
            def kind(term): return "named" if term.startswith("<") else term.split("(", 1)[0]
            return kind(left) + "->" + kind(right)
    return "malformed"

with open(path, encoding="utf-8") as source:
    for number, raw in enumerate(source, 1):
        line = raw.strip()
        if line.startswith("Declaration("):
            match = re.match(r"Declaration\(([^()]+)\(", line)
            declarations[match.group(1) if match else "malformed"] += 1
            late_declarations += first_axiom is not None
        elif line.startswith("SubClassOf("):
            first_axiom = first_axiom or number
            shape = outer_term(line)
            counts[shape] += 1
            examples.setdefault(shape, line[:600])
print(json.dumps({
    "ontology": 9794,
    "declarations": dict(sorted(declarations.items())),
    "first_axiom_line": first_axiom,
    "late_declarations": late_declarations,
    "subclass_shapes": dict(sorted(counts.items())),
    "examples": {key: examples[key] for key in sorted(examples)},
}, sort_keys=True))
print("ORE9794_SHAPE_COMPLETE")
PY
