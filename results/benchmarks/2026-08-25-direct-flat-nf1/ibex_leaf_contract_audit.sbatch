#!/bin/bash
#SBATCH --job-name=km-leaf-contract
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/leaf-contract-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections
import json
import re

ids = [8737, 15059, 16744, 14042, 1559]
root = "/ibex/scratch/hohndor/km/corpus"
for oid in ids:
    declarations = collections.Counter()
    first_axiom = None
    declarations_after_axiom = 0
    line_number = 0
    with open(f"{root}/ore_ont_{oid}.owl", encoding="utf-8") as source:
        for raw in source:
            line_number += 1
            line = raw.strip()
            if line.startswith("Declaration("):
                match = re.match(r"Declaration\(([^()]+)\(", line)
                declarations[match.group(1) if match else "malformed"] += 1
                if first_axiom is not None:
                    declarations_after_axiom += 1
            elif line.startswith((
                "SubClassOf(", "SubObjectPropertyOf(",
                "InverseObjectProperties(", "EquivalentObjectProperties(",
                "SymmetricObjectProperty(", "TransitiveObjectProperty(",
                "ReflexiveObjectProperty(",
            )) and first_axiom is None:
                first_axiom = line_number
    print(json.dumps({
        "ontology": oid,
        "declarations": dict(sorted(declarations.items())),
        "first_logical_axiom_line": first_axiom,
        "declarations_after_axiom": declarations_after_axiom,
    }, sort_keys=True))
print("LEAF_CONTRACT_AUDIT_COMPLETE")
PY
