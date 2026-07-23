#!/bin/bash
# Audit and aggregate the exactly-30-task ORE rerun.
#SBATCH --job-name=km-panel30-aggregate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260723-rerun/slurm-%x-%j.out

set -euo pipefail
[[ $# -eq 4 ]] || {
    echo "usage: sbatch ibex_aggregate_full_panel_chunked.sbatch RUN_ID HISTORICAL_LEDGER OUTPUT_DIR DRIVER_MANIFEST" >&2
    exit 2
}

run_id=$1
historical_ledger=$(/usr/bin/readlink -f "$2")
output_dir=$(/usr/bin/readlink -m "$3")
driver_manifest=$(/usr/bin/readlink -f "$4")
[[ $run_id =~ ^[0-9]+$ ]]
[[ -s $historical_ledger ]]
[[ -s $driver_manifest ]]
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?missing Slurm submit directory}")
deployment_root=/ibex/scratch/hohndor/km/full-panel-20260723-rerun

export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
/usr/bin/mkdir -p "$output_dir"

# This gate proves that every historically accepted environment is exercised
# by the frozen contract before measurements can be aggregated or reported.
/usr/bin/python3 "$script_dir/audit_full_panel_route_coverage.py" \
    --ledger "$historical_ledger" \
    --contract "$script_dir/full_panel_contract.py" \
    --output "$output_dir/route-coverage-audit.json"

# The aggregator discards all provisional correctness labels and recomputes
# them with the hash-bound semantic scorer before writing any summary.
/usr/bin/python3 "$script_dir/aggregate_full_panel.py" \
    --run-root "$deployment_root/runs/$run_id" \
    --ontology-list /ibex/scratch/hohndor/km/routing_20260715/onts.txt \
    --existing-wide "$historical_ledger" \
    --output-dir "$output_dir" \
    --array-driver-manifest "$driver_manifest" \
    --supplemental-driver-manifest "$driver_manifest" \
    --build-receipt "$deployment_root/build/build-receipt.json" \
    --binary-manifest "$deployment_root/build/binaries.sha256" \
    --ablation-patches-manifest "$deployment_root/build/ablation-patches.sha256" \
    --adjudication-4669-manifest "$deployment_root/aggregation-input/4669-targeted-satisfiability/evidence-files.sha256" \
    --route-audit "$output_dir/route-coverage-audit.json" \
    --chunk-count 30
