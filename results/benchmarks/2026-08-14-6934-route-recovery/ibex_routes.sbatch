#!/bin/bash
#SBATCH --job-name=km-6934-route-recovery
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/route-6934-v020-20260814/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/route-6934-v020-20260814
binary=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/km-combined
expected=a18fa4026561768dfc50df93904ba44ef98bfd525d0be9c4b165f4fede3b89a7
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
runner=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/inproc-4m-sweep/full_panel_run_one.py
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz
mkdir -p "$root/results" "$root/failures"

run_arm() {
  local arm=$1
  shift
  local work=${SLURM_TMPDIR:-/tmp}/km-6934-$arm-$SLURM_JOB_ID
  PYTHONPATH=$(dirname "$runner") /usr/bin/python3 "$runner" \
    --kind km --arm "$arm" --ontology "$ontology" --binary "$binary" \
    --workers 16 --timeout 240 --memcap-mb 20480 --gold "$gold" \
    --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
    --checkpoint "$root/results/$arm.checkpoint.json" --capture-km-route \
    "$@" > "$root/results/$arm.json"
  jq -c '{arm,status,verdict,wall_s,peak_mb,signature_sha256,selected_route_trace,binary_sha256}' "$root/results/$arm.json"
}

run_arm htforce_race \
  --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
  --env KM_HT_MEM_GB=18 --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_ABSORB=1 \
  --env KM_ABSORB_PORTFOLIO=1 --env KM_HT_FORCE=1 --env KM_HT_MODE=race
run_arm ht_full --env KM_ROUTE=ht_full
run_arm nominal_ni_abox --env KM_ROUTE=nominal_ni_abox
