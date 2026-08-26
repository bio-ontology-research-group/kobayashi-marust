#!/usr/bin/env bash
#SBATCH --job-name=km-v19-15803-projection
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/projection-15803-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826
baseline=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/km
candidate=$root/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_15803.owl
work=${SLURM_TMPDIR:-/tmp}/km-v19-15803-${SLURM_JOB_ID}
mkdir -p "$work" "$root/projection-15803-results"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$baseline" | awk '{print $1}') == 86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559 ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == 760ffd875e5ac72f0aa0f205a46add71250410280725f5042a375c01cb67bd10 ]]

/usr/bin/python3 - "$input" "$work/projected.ofn" <<'PY'
import pathlib, sys
source, target = map(pathlib.Path, sys.argv[1:])
removed = 0
with source.open() as inp, target.open("w") as out:
    for raw in inp:
        line = raw.strip()
        drop = line.startswith(("EquivalentClasses(", "DisjointClasses(")) or (
            line.startswith("SubClassOf(<") and " ObjectIntersectionOf(" in line
        )
        if drop:
            removed += 1
        else:
            out.write(raw)
print(f"removed={removed}")
if removed != 72:
    raise SystemExit(f"unexpected removed axiom count: {removed}")
PY

for arm in original projected; do
  if [[ $arm == original ]]; then binary=$baseline; ont=$input; else binary=$candidate; ont=$work/projected.ofn; fi
  /usr/bin/time -f '%e\t%M\t%x' -o "$work/${arm}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$ont" \
    > "$work/${arm}.json" 2> "$work/${arm}.stderr"
  read -r wall rss rc < "$work/${arm}.measure"
  [[ $rc == 0 && -s "$work/${arm}.json" ]]
  printf 'RESULT\tarm=%s\twall_s=%s\trss_kib=%s\n' "$arm" "$wall" "$rss"
done

/usr/bin/python3 - "$work/original.json" "$work/projected.json" "$root/projection-15803-results/diff-summary.json" <<'PY'
import json, pathlib, sys
original_path, projected_path, summary_path = map(pathlib.Path, sys.argv[1:])
original = json.load(original_path.open())
projected = json.load(projected_path.open())
orig_pairs = {tuple(pair) for pair in original["subsumptions"]}
proj_pairs = {tuple(pair) for pair in projected["subsumptions"]}
missing = sorted(orig_pairs - proj_pairs)
extra = sorted(proj_pairs - orig_pairs)
summary = {
    "original_pairs": len(orig_pairs),
    "projected_pairs": len(proj_pairs),
    "missing": len(missing),
    "extra": len(extra),
    "missing_sample": missing[:200],
    "extra_sample": extra[:200],
}
summary_path.write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
PY
for suffix in measure stderr; do
  install -m 644 "$work/original.$suffix" "$root/projection-15803-results/original.$suffix"
  install -m 644 "$work/projected.$suffix" "$root/projection-15803-results/projected.$suffix"
done
echo PROJECTION_COMPLETE
