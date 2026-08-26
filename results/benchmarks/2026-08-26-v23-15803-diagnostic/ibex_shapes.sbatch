#!/usr/bin/env bash
#SBATCH --job-name=km-15803-shapes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:03:00
#SBATCH --output=/ibex/scratch/hohndor/km/v23-15803-diagnostic-20260826/shapes-%j.out
set -euo pipefail
input=/ibex/scratch/hohndor/km/corpus/ore_ont_15803.owl
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
/usr/bin/python3 - "$input" <<'PY'
import collections
import sys

tokens = (
    "ObjectIntersectionOf(", "ObjectUnionOf(", "ObjectOneOf(",
    "DisjointClasses(", "EquivalentClasses(", "ObjectComplementOf(",
)
counts = collections.Counter()
selected = []
with open(sys.argv[1], encoding="utf-8") as source:
    for lineno, raw in enumerate(source, 1):
        line = raw.strip()
        hits = tuple(token for token in tokens if token in line)
        for token in hits:
            counts[token] += 1
        if hits:
            selected.append((lineno, line))
print("COUNTS", dict(counts))
print("SELECTED", len(selected))
for lineno, line in selected:
    print(f"LINE\t{lineno}\t{line}")
print("TASK_COMPLETE")
PY
