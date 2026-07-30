#!/bin/bash
# Compare historical and current ELC workers on byte-identical frontend input.
#SBATCH --job-name=km-v7-3524-elc-diff
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=128G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-elc-diff/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
old=/ibex/scratch/hohndor/km/routing_20260715/special-iri-main-20260718/target/release/km
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl
out=$root/diagnostic-3524-elc-diff
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-elc-diff-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$out" "$work"

KM_ROUTE=elc KM_NO_BOTTOM_PREPASS=1 \
  "$root/km" ofn "$ont" --meta "$work/meta.json" > "$work/clauses.json"

set +e
KM_ELC_TIMING=1 timeout 240 /usr/bin/time -v \
  "$old" elc < "$work/clauses.json" > "$work/historical.json" \
  2> "$out/historical.log"
historical_rc=$?
KM_ELC_TIMING=1 timeout 240 /usr/bin/time -v \
  "$root/km" elc < "$work/clauses.json" > "$work/current.json" \
  2> "$out/current.log"
current_rc=$?
set -e

/usr/bin/python3 - "$work" "$historical_rc" "$current_rc" \
  > "$out/receipt.json.tmp" <<'PY'
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
row = {}
for version, rc in (("historical", int(sys.argv[2])), ("current", int(sys.argv[3]))):
    path = root / f"{version}.json"
    row[version] = {
        "rc": rc,
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }
row["outputs_identical"] = (
    row["historical"]["rc"] == 0
    and row["current"]["rc"] == 0
    and row["historical"]["sha256"] == row["current"]["sha256"]
)
print(json.dumps(row, sort_keys=True))
PY
/usr/bin/mv "$out/receipt.json.tmp" "$out/receipt.json"
echo "ELC_WORKER_DIFFERENTIAL_COMPLETE"
