#!/usr/bin/env bash
#SBATCH --job-name=km-v17-3377-projection
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --output=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826/projection-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v17-large-source-shapes-20260826
binary=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/km
binary_sha=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
input=/ibex/scratch/hohndor/km/corpus/ore_ont_3377.owl
work=${SLURM_TMPDIR:-/tmp}/km-v17-3377-${SLURM_JOB_ID}
mkdir -p "$work" "$root/projection-results"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$binary_sha" ]]

/usr/bin/python3 - "$input" "$work/projected.ofn" <<'PY'
import pathlib, sys
source, target = map(pathlib.Path, sys.argv[1:])
keep_heads = {
    "Prefix", "Ontology", "Declaration", "SubObjectPropertyOf",
    "TransitiveObjectProperty", "SymmetricObjectProperty",
    "InverseObjectProperties",
}
with source.open() as inp, target.open("w") as out:
    for raw in inp:
        line = raw.strip()
        head = line.split("(", 1)[0]
        keep = not line or line == ")" or head in keep_heads
        if head == "SubClassOf":
            body = line[len("SubClassOf("):-1]
            keep = body.startswith("<")
        if keep:
            out.write(raw)
PY

for arm in original projected; do
  if [[ $arm == original ]]; then ont=$input; else ont=$work/projected.ofn; fi
  /usr/bin/time -f '%e\t%M\t%x' -o "$work/${arm}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$ont" \
    > "$work/${arm}.json" 2> "$work/${arm}.stderr"
  read -r wall rss rc < "$work/${arm}.measure"
  [[ $rc == 0 && -s "$work/${arm}.json" ]]
  printf 'RESULT\tarm=%s\twall_s=%s\trss_kib=%s\n' "$arm" "$wall" "$rss"
done
for suffix in measure json stderr; do
  install -m 644 "$work/original.$suffix" "$root/projection-results/original.$suffix"
  install -m 644 "$work/projected.$suffix" "$root/projection-results/projected.$suffix"
done
cmp "$work/original.json" "$work/projected.json"
echo EXACT_MATCH
