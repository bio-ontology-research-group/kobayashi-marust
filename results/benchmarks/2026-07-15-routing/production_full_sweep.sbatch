#!/bin/bash
# One-ontology-per-allocation production-route sweep. Required submit exports:
# SWEEP_TAG and SWEEP_KM. Results publish atomically only after a JSON sanity
# check, making interrupted arrays safely resumable.
#SBATCH --job-name=km-prod-sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%100
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/prod-%A_%a.out

set -euo pipefail

: "${SWEEP_TAG:?submit with --export=ALL,SWEEP_TAG=...}"
: "${SWEEP_KM:?submit with --export=ALL,SWEEP_KM=...}"

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix-3b1d2a87.py
gold_dir=$km_root/gold
result_dir=$root/production-sweeps/$SWEEP_TAG/results
failure_dir=$root/production-sweeps/$SWEEP_TAG/failures
manifest_dir=$root/production-sweeps/$SWEEP_TAG/manifests
work=${SLURM_TMPDIR:-/tmp}/km-prod-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

mapfile -t onts < "$root/onts.txt"
[[ ${#onts[@]} -eq 592 ]] || { echo "expected 592 ontologies" >&2; exit 2; }
ontology=${onts[${SLURM_ARRAY_TASK_ID:-0}]}
ontology_path=$km_root/corpus/$ontology
gold=$gold_dir/konclude__$ontology.sig.gz
result=$result_dir/$ontology.jsonl
tmp=$result.partial.${SLURM_JOB_ID}

/usr/bin/mkdir -p "$result_dir" "$failure_dir" "$manifest_dir" "$work"
[[ -s "$SWEEP_KM" && -s "$runner" && -s "$ontology_path" ]] \
  || { echo "missing sweep input for $ontology" >&2; exit 2; }

if [[ -s "$result" ]] && /usr/bin/python3 - "$result" "$ontology" <<'PY'
import json, sys
rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
assert len(rows) == 1
assert rows[0]["ont"] == sys.argv[2]
assert rows[0]["arm"] == "production_all"
PY
then
  echo "SKIP complete ontology=$ontology"
  exit 0
fi

case "$ontology" in
  ore_ont_10860.owl|ore_ont_1194.owl|ore_ont_15703.owl|ore_ont_3524.owl|ore_ont_4669.owl)
    gold_args=(--gold-kind none)
    ;;
  *)
    [[ -s "$gold" ]] || { echo "missing gold: $gold" >&2; exit 2; }
    gold_args=(--gold "$gold" --gold-kind konclude)
    ;;
esac

km_sha=$(/usr/bin/sha256sum "$SWEEP_KM" | /usr/bin/cut -d' ' -f1)
{
  echo "job_id=$SLURM_JOB_ID"
  echo "array_task_id=$SLURM_ARRAY_TASK_ID"
  echo "ontology=$ontology"
  echo "km=$SWEEP_KM"
  echo "km_sha=$km_sha"
  echo "host=$(hostname)"
} > "$manifest_dir/$ontology.txt"

/usr/bin/python3 "$runner" \
  --kind km --arm production_all --ontology "$ontology_path" \
  --binary "$SWEEP_KM" --binary-sha "$km_sha" \
  "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir" \
  --order-index 0 --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=production_all > "$tmp"

/usr/bin/python3 - "$tmp" "$ontology" <<'PY'
import json, sys
rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
assert len(rows) == 1
row = rows[0]
assert row["ont"] == sys.argv[2]
assert row["arm"] == "production_all"
assert row.get("binary_sha256")
assert row.get("status")
PY

/usr/bin/mv "$tmp" "$result"
/usr/bin/rm -rf "$work"
echo "DONE ontology=$ontology"
