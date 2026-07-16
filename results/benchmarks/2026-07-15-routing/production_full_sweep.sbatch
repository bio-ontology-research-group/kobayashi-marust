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
# The reasoner is measured at a 20 GiB cap. Ordinary workers get modest
# supervisor headroom; a whole-step OOM is finalized separately and only from
# explicit Slurm OOM evidence.
#SBATCH --mem=28G
#SBATCH --array=0-591%100
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/prod-%A_%a.out

set -euo pipefail

: "${SWEEP_TAG:?submit with --export=ALL,SWEEP_TAG=...}"
: "${SWEEP_KM:?submit with --export=ALL,SWEEP_KM=...}"

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix-ca86b612.py
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
# Durable, attempt-independent path the watchdog publishes the terminal row to
# BEFORE it kills the reasoner. If the Slurm cgroup OOM-killer takes the whole
# step (supervisor included) on a later line, this file already holds the memout
# row and the next array attempt salvages it instead of blowing up forever.
ckpt=$result.ckpt

/usr/bin/mkdir -p "$result_dir" "$failure_dir" "$manifest_dir" "$work"
[[ -s "$SWEEP_KM" && -s "$runner" && -s "$ontology_path" ]] \
  || { echo "missing sweep input for $ontology" >&2; exit 2; }
km_sha=$(/usr/bin/sha256sum "$SWEEP_KM" | /usr/bin/cut -d' ' -f1)

# One publishable row per ontology: exactly one JSON object naming this
# ontology and arm, with a status and a binary hash. A memout row satisfies
# this too, so a genuine 20 GB blow-up publishes and is never retried forever.
validate_row() {
  /usr/bin/python3 - "$1" "$ontology" "$km_sha" <<'PY'
import json, sys
try:
    rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
except (OSError, ValueError):
    sys.exit(1)
if len(rows) != 1:
    sys.exit(1)
row = rows[0]
sys.exit(0 if (row.get("ont") == sys.argv[2]
               and row.get("arm") == "production_all"
               and row.get("binary_sha256") == sys.argv[3]
               and row.get("status") in
                   {"ok", "timeout", "memout", "unsupported"}) else 1)
PY
}

if [[ -s "$result" ]] && validate_row "$result"; then
  echo "SKIP complete ontology=$ontology"
  /usr/bin/rm -f "$ckpt"
  exit 0
fi

# Recover a memout/terminal row a previous attempt's watchdog durably wrote just
# before a whole-cgroup OOM kill of that attempt's supervisor.
if [[ -s "$ckpt" ]] && validate_row "$ckpt"; then
  /usr/bin/mv "$ckpt" "$result"
  echo "SALVAGE prior-attempt checkpoint ontology=$ontology"
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

{
  echo "job_id=$SLURM_JOB_ID"
  echo "array_task_id=$SLURM_ARRAY_TASK_ID"
  echo "ontology=$ontology"
  echo "km=$SWEEP_KM"
  echo "km_sha=$km_sha"
  echo "host=$(hostname)"
} > "$manifest_dir/$ontology.txt"

# The measured reasoner cap stays at 20 GiB (--memcap-mb 20480); the step's
# extra memory is supervisor headroom, not part of the KM allowance. The
# watchdog normally writes --checkpoint before killing an over-cap process
# tree. If a descendant allocation spike kills the whole step first, leave the
# row absent for finalize_oom_rows.py to adjudicate from the Slurm log. Do not
# let a SIGKILLed runner abort the task under set -e: capture its rc below.
set +e
/usr/bin/python3 "$runner" \
  --kind km --arm production_all --ontology "$ontology_path" \
  --binary "$SWEEP_KM" --binary-sha "$km_sha" \
  "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir" \
  --checkpoint "$ckpt" \
  --order-index 0 --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=production_all > "$tmp"
runner_rc=$?
set -e

if validate_row "$tmp"; then
  /usr/bin/mv "$tmp" "$result"
  /usr/bin/rm -f "$ckpt"
  /usr/bin/rm -rf "$work"
  echo "DONE ontology=$ontology rc=$runner_rc"
  exit 0
fi

# The runner produced no usable stdout row (killed after emitting its durable
# checkpoint, or the OOM-killer took only the runner). Publish the checkpoint.
if [[ -s "$ckpt" ]] && validate_row "$ckpt"; then
  /usr/bin/mv "$ckpt" "$result"
  /usr/bin/rm -f "$tmp"
  /usr/bin/rm -rf "$work"
  echo "SALVAGE checkpoint ontology=$ontology rc=$runner_rc"
  exit 0
fi

echo "NO-ROW ontology=$ontology rc=$runner_rc (resumable)" >&2
/usr/bin/rm -f "$tmp"
/usr/bin/rm -rf "$work"
exit 1
