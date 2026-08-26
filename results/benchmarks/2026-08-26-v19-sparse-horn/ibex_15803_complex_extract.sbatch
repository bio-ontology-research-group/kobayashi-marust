#!/usr/bin/env bash
#SBATCH --job-name=km-v19-15803-complex
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:03:00
#SBATCH --output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/complex-15803-%j.out

set -euo pipefail
input=/ibex/scratch/hohndor/km/corpus/ore_ont_15803.owl
output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/ore_15803_complex_axioms.txt
/usr/bin/python3 - "$input" "$output" <<'PY'
import pathlib, sys
source, output = map(pathlib.Path, sys.argv[1:])
selected = []
for raw in source.open(errors="strict"):
    line = raw.strip()
    if line.startswith(("EquivalentClasses(", "DisjointClasses(")) or (
        line.startswith("SubClassOf(<") and " ObjectIntersectionOf(" in line
    ):
        selected.append(line)
output.write_text("\n".join(selected) + "\n")
print(f"selected={len(selected)} bytes={output.stat().st_size}")
PY
[[ $(/usr/bin/wc -l < "$output") -eq 72 ]]
echo EXTRACT_COMPLETE
