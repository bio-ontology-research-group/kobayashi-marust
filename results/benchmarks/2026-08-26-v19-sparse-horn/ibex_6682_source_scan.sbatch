#!/usr/bin/env bash
#SBATCH --job-name=km-v19-6682-shape
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --time=00:05:00
#SBATCH --output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/source-scan-%j.out

set -euo pipefail
input=/ibex/scratch/hohndor/km/corpus/ore_ont_6682.owl
output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/ore_6682_source_shape.json
/usr/bin/python3 - "$input" "$output" <<'PY'
import collections, json, pathlib, sys

source, output = map(pathlib.Path, sys.argv[1:])
counts = collections.Counter()
examples = collections.defaultdict(list)
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
    else:
        key = f"axiom:{head}"
    if len(examples[key]) < 8:
        examples[key].append(line[:2000])

result = {
    "ontology": source.name,
    "bytes": source.stat().st_size,
    "counts": dict(sorted(counts.items())),
    "examples": dict(sorted(examples.items())),
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, indent=2, sort_keys=True))
PY
test -s "$output"
echo SCAN_COMPLETE
