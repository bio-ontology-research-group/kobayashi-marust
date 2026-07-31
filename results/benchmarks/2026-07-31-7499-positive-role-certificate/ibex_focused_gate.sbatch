#!/bin/bash
# Source-bound focused production gate for commit 9462131. Submit only after
# the build job has published PROOF_ROOT/km.
#SBATCH --job-name=km-7499-cert-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --array=0-4%1
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/7499-cert-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
km_root=/ibex/scratch/hohndor/km
proof_root=$root/7499-positive-role-9462131
runner=$root/bench_one_matrix-392f90aa.py
binary=$proof_root/km
result_dir=$proof_root/focused-results
failure_dir=$proof_root/focused-failures
work=${SLURM_TMPDIR:-/tmp}/km-7499-cert-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
onts=(
  ore_ont_7499.owl
  ore_ont_33.owl
  ore_ont_10702.owl
  ore_ont_6934.owl
  ore_ont_9540.owl
)

ontology=${onts[$SLURM_ARRAY_TASK_ID]}
ontology_path=$km_root/corpus/$ontology
gold=$km_root/gold/konclude__$ontology.sig.gz
result=$result_dir/$ontology.jsonl
tmp=$result.partial.$SLURM_JOB_ID

/usr/bin/mkdir -p "$result_dir" "$failure_dir" "$work"
for path in "$binary" "$runner" "$ontology_path" "$gold"; do
  [[ -s "$path" ]] || { echo "missing gate input: $path" >&2; exit 2; }
done
binary_sha=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)

set +e
/usr/bin/python3 "$runner" \
  --kind km --arm auto --ontology "$ontology_path" \
  --binary "$binary" --binary-sha "$binary_sha" \
  --gold "$gold" --gold-kind konclude \
  --workdir "$work" --failures-dir "$failure_dir" \
  --order-index "$SLURM_ARRAY_TASK_ID" --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=auto > "$tmp"
runner_rc=$?
set -e

/usr/bin/python3 - "$tmp" "$ontology" "$binary_sha" <<'PY'
import json
import sys

rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
if len(rows) != 1:
    raise SystemExit(f"expected one result row, found {len(rows)}")
row = rows[0]
if row.get("ont") != sys.argv[2] or row.get("arm") != "auto":
    raise SystemExit(f"wrong result identity: {row}")
if row.get("binary_sha256") != sys.argv[3]:
    raise SystemExit("binary hash mismatch")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"focused gate failed: {row}")
PY

/usr/bin/mv "$tmp" "$result"
/usr/bin/rm -rf "$work"
echo "GATE_OK ontology=$ontology runner_rc=$runner_rc binary_sha=$binary_sha"
