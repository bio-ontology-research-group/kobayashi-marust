#!/usr/bin/env bash
#SBATCH --job-name=km-v17-3377-diff
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --time=00:05:00
#SBATCH --output=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826/diff-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826
input=/ibex/scratch/hohndor/km/corpus/ore_ont_3377.owl
original=$root/projection-results/original.json
projected=$root/projection-results/projected.json
/usr/bin/python3 - "$input" "$original" "$projected" "$root/projection-results" <<'PY'
import json, pathlib, sys
source, original_path, projected_path, outdir = map(pathlib.Path, sys.argv[1:])
complex_rules = []
for raw in source.open():
    line = raw.strip()
    if line.startswith("SubClassOf(") and not line[len("SubClassOf("):].startswith("<"):
        complex_rules.append(line)
(outdir / "complex-lhs.txt").write_text("\n".join(complex_rules) + "\n")

original = json.load(original_path.open())
projected = json.load(projected_path.open())
orig_pairs = {tuple(pair) for pair in original["subsumptions"]}
proj_pairs = {tuple(pair) for pair in projected["subsumptions"]}
missing = sorted(orig_pairs - proj_pairs)
extra = sorted(proj_pairs - orig_pairs)
summary = {
    "complex_rules": len(complex_rules),
    "original_pairs": len(orig_pairs),
    "projected_pairs": len(proj_pairs),
    "missing": len(missing),
    "extra": len(extra),
    "missing_sample": missing[:100],
    "extra_sample": extra[:100],
}
(outdir / "diff-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
PY
