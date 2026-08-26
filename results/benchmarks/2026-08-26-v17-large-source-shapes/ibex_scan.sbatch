#!/usr/bin/env bash
#SBATCH --job-name=km-v17-source-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --time=00:05:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826/scan-%A_%a.out

set -euo pipefail
onts=(3377 15803)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
root=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826
mkdir -p "$root/results"
/usr/bin/python3 - "$input" "$root/results/ore_${ont}.json" <<'PY'
import collections, json, pathlib, re, sys

source, output = map(pathlib.Path, sys.argv[1:])
counts = collections.Counter()
examples = {}
for raw in source.open(errors="strict"):
    line = raw.strip()
    if not line:
        continue
    head = line.split("(", 1)[0]
    counts[f"axiom:{head}"] += 1
    if head == "SubClassOf":
        body = line[len("SubClassOf("):-1]
        lhs = "named" if body.startswith("<") else body.split("(", 1)[0]
        if lhs == "named":
            depth = 0
            split = None
            for i, ch in enumerate(body):
                depth += ch == "("
                depth -= ch == ")"
                if ch == " " and depth == 0:
                    split = i
                    break
            rhs = body[split + 1:] if split is not None else "malformed"
            rhs_shape = "named" if rhs.startswith("<") else rhs.split("(", 1)[0]
        else:
            rhs_shape = "unknown"
        key = f"subclass:{lhs}->{rhs_shape}"
        counts[key] += 1
        examples.setdefault(key, line[:1000])
    elif head in {"EquivalentClasses", "DisjointClasses", "ClassAssertion",
                  "DifferentIndividuals", "SubObjectPropertyOf",
                  "TransitiveObjectProperty"}:
        examples.setdefault(f"axiom:{head}", line[:1000])

result = {
    "ontology": source.name,
    "bytes": source.stat().st_size,
    "counts": dict(sorted(counts.items())),
    "examples": dict(sorted(examples.items())),
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, indent=2, sort_keys=True))
PY
