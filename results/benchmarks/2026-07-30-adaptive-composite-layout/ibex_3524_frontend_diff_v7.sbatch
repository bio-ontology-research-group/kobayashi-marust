#!/bin/bash
# Compare current and historically exact frontend outputs for ontology 3524.
#SBATCH --job-name=km-v7-3524-ofn-diff
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-ofn-diff/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
old=/ibex/scratch/hohndor/km/routing_20260715/special-iri-main-20260718/target/release/km
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl
out=$root/diagnostic-3524-ofn-diff
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-ofn-diff-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$out" "$work"

for version in current historical; do
  if [[ $version == current ]]; then
    binary=$root/km
  else
    binary=$old
  fi
  KM_ROUTE=elc KM_NO_BOTTOM_PREPASS=1 \
    "$binary" ofn "$ont" --meta "$work/$version.meta.json" \
    > "$work/$version.clauses.json"
done

/usr/bin/python3 - "$work" > "$out/receipt.json.tmp" <<'PY'
import hashlib
import json
import pathlib
import sys

def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

root = pathlib.Path(sys.argv[1])
rows = {}
for version in ("current", "historical"):
    clauses = root / f"{version}.clauses.json"
    meta = root / f"{version}.meta.json"
    rows[version] = {
        "clauses_bytes": clauses.stat().st_size,
        "clauses_sha256": sha256(clauses),
        "meta_bytes": meta.stat().st_size,
        "meta_sha256": sha256(meta),
    }
rows["clauses_identical"] = (
    rows["current"]["clauses_sha256"] == rows["historical"]["clauses_sha256"]
)
print(json.dumps(rows, sort_keys=True))
PY
/usr/bin/mv "$out/receipt.json.tmp" "$out/receipt.json"
echo "FRONTEND_DIFFERENTIAL_COMPLETE"
