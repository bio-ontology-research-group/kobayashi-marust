#!/bin/bash
# Validate and aggregate one completed 592-ontology full-panel run.
#SBATCH --job-name=km-panel-aggregate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260722/slurm-%x-%j.out

set -euo pipefail
[[ $# -eq 5 ]] || {
    echo "usage: sbatch ibex_aggregate_full_panel.sbatch RUN_ID EXISTING_WIDE OUTPUT_DIR ARRAY_DRIVER_MANIFEST SUPPLEMENTAL_DRIVER_MANIFEST" >&2
    exit 2
}

run_id=$1
existing_wide=$(/usr/bin/readlink -f "$2")
output_dir=$(/usr/bin/readlink -m "$3")
array_driver_manifest=$(/usr/bin/readlink -f "$4")
supplemental_driver_manifest=$(/usr/bin/readlink -f "$5")
[[ $run_id =~ ^[0-9]+$ ]]
[[ -s $existing_wide ]]
[[ -s $array_driver_manifest ]]
[[ -s $supplemental_driver_manifest ]]
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?missing Slurm submit directory}")
root=/ibex/scratch/hohndor/km

export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
/usr/bin/python3 "$script_dir/aggregate_full_panel.py" \
    --run-root "$root/full-panel-20260722/runs/$run_id" \
    --ontology-list "$root/routing_20260715/onts.txt" \
    --existing-wide "$existing_wide" \
    --output-dir "$output_dir" \
    --array-driver-manifest "$array_driver_manifest" \
    --supplemental-driver-manifest "$supplemental_driver_manifest" \
    --build-receipt "$root/full-panel-20260722/build/build-receipt.json" \
    --binary-manifest "$root/full-panel-20260722/build/binaries.sha256" \
    --ablation-patches-manifest "$root/full-panel-20260722/build/ablation-patches.sha256" \
    --adjudication-4669-manifest "$root/full-panel-20260722/aggregation-input/4669-targeted-satisfiability/evidence-files.sha256"
