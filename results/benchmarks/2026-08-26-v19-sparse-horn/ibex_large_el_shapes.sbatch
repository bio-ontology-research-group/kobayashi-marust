#!/usr/bin/env bash
#SBATCH --job-name=km-v19-large-el-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:04:00
#SBATCH --array=0-11%6
#SBATCH --output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/el-shape-%A_%a.out

set -euo pipefail
onts=(7246 10073 11315 3560 6223 9499 1579 6477 5519 15976 16596 7868)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/el-shape-${ont}.json
/usr/bin/python3 - "$input" "$output" <<'PY'
import collections, json, pathlib, sys
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
        key = f"subclass:{lhs}->{rhs_shape}"
        counts[key] += 1
        examples.setdefault(key, line[:1200])
    elif head not in {"Prefix", "Ontology", "Declaration", ")"}:
        examples.setdefault(f"axiom:{head}", line[:1200])
result = {
    "ontology": source.name,
    "bytes": source.stat().st_size,
    "counts": dict(sorted(counts.items())),
    "examples": dict(sorted(examples.items())),
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, sort_keys=True))
PY
test -s "$output"
echo SCAN_COMPLETE
