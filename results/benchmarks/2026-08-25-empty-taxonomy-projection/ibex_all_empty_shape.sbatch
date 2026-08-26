#!/bin/bash
#SBATCH --job-name=km-all-empty-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-source-audit-20260825/all-empty-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import glob
import json
import os
import re

results = "/ibex/scratch/hohndor/km/v036-large-clean-20260815/full-pair/results"
corpus = "/ibex/scratch/hohndor/km/corpus"
empty = []
for path in glob.glob(results + "/*.json"):
    if path.endswith(".checkpoint.json"):
        continue
    row = json.load(open(path))
    if (str(row.get("arm", "")).endswith("candidate")
            and row.get("status") == "ok"
            and row.get("subsumptions") == 0
            and row.get("unsatisfiable") == 0):
        empty.append(row["ont"])
assert len(empty) == 83 and len(set(empty)) == 83, len(empty)

named_edge = re.compile(r"^SubClassOf\(<[^<>\s]+> <[^<>\s]+>\)$")
leaf = re.compile(
    r"^SubClassOf\(<[^<>\s]+> ObjectSomeValuesFrom\(<[^<>\s]+> <[^<>\s]+>\)\)$")
declaration = re.compile(r"^Declaration\((Class|ObjectProperty)\(<[^<>\s]+>\)\)$")
unary_role = re.compile(r"^(Transitive|Symmetric)ObjectProperty\(<[^<>\s]+>\)$")
binary_role = re.compile(
    r"^(SubObjectPropertyOf|InverseObjectProperties|EquivalentObjectProperties)"
    r"\(<[^<>\s]+> <[^<>\s]+>\)$")

eligible = []
for ontology in sorted(empty, key=lambda name: int(name.split("_")[-1].split(".")[0])):
    path = f"{corpus}/{ontology}"
    counts = {"declaration": 0, "named_edge": 0, "leaf": 0, "rbox": 0, "other": 0}
    first_other = None
    saw_axiom = False
    late_declaration = False
    with open(path, encoding="utf-8") as source:
        for number, raw in enumerate(source, 1):
            line = raw.strip()
            if not line or line == ")" or line.startswith("Prefix(") or line.startswith("Ontology("):
                continue
            if declaration.match(line):
                counts["declaration"] += 1
                late_declaration |= saw_axiom
            elif named_edge.match(line):
                counts["named_edge"] += 1
                saw_axiom = True
            elif leaf.match(line):
                counts["leaf"] += 1
                saw_axiom = True
            elif unary_role.match(line) or binary_role.match(line):
                counts["rbox"] += 1
                saw_axiom = True
            else:
                counts["other"] += 1
                first_other = first_other or {"line": number, "text": line[:300]}
                saw_axiom = True
    accepted_shape = (
        os.path.getsize(path) >= 32 << 20
        and counts["other"] == 0
        and not late_declaration
        and counts["declaration"] >= 1_000
        and counts["named_edge"] + counts["leaf"] + counts["rbox"] > 0
    )
    if accepted_shape:
        eligible.append(ontology)
    print(json.dumps({
        "ontology": ontology,
        "bytes": os.path.getsize(path),
        "counts": counts,
        "late_declaration": late_declaration,
        "accepted_lexical_shape": accepted_shape,
        "first_other": first_other,
    }, sort_keys=True))
print(json.dumps({"empty": len(empty), "eligible": eligible, "eligible_count": len(eligible)}, sort_keys=True))
print("ALL_EMPTY_SHAPES_COMPLETE")
PY
