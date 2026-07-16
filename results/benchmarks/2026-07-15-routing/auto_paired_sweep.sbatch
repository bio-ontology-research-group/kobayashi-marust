#!/bin/bash
# Final end-to-end validation of the generated default route. Each ontology's
# automatic KM run and both Konclude references share one exclusive CPU model.
# Their order rotates to control warm-cache and first-process effects.
#SBATCH --job-name=km-auto-paired
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%36
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/auto-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one.py
km=$root/km-auto-final
kon=$km_root/Konclude-official
gold_dir=$km_root/gold
result_dir=$root/auto-paired-results
failure_dir=$root/auto-failures
mkdir -p "$result_dir" "$failure_dir" "$root/slurm"

mapfile -t ontologies < "$root/onts.txt"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
source_ontology=$km_root/corpus/$ontology
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$source_ontology" "$local_ontology"

result=$result_dir/$ontology.jsonl
gold=$gold_dir/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-auto-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
mkdir -p "$work"
: > "$result"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)

run_km() {
  /usr/bin/python3 "$runner" \
    --kind km --arm auto --ontology "$local_ontology" \
    --binary "$km" --binary-sha "$km_sha" --gold "$gold" \
    --workdir "$work" --failures-dir "$failure_dir" \
    --keep-artifacts \
    --order-index "$1" --timeout 240 --memcap-mb 20480 \
    --env KM_ROUTE=auto --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
    --env KM_HT_MEM_GB=18 --env KM_KEEP_CHAIN_AXIOMS=1 \
    --env KM_TIMING=1 --env KM_OFN_TIMING=1 >> "$result"
}

run_konclude() {
  local workers=$1
  local position=$2
  /usr/bin/python3 "$runner" \
    --kind konclude --arm "konclude_w${workers}" \
    --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
    --workers "$workers" --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$position" --timeout 240 --memcap-mb 20480 >> "$result"
}

case $((SLURM_ARRAY_TASK_ID % 3)) in
  0)
    run_konclude 1 0
    run_km 1
    run_konclude 16 2
    ;;
  1)
    run_km 0
    run_konclude 16 1
    run_konclude 1 2
    ;;
  2)
    run_konclude 16 0
    run_konclude 1 1
    run_km 2
    ;;
esac

/usr/bin/rm -rf "$work" "$local_ontology"
