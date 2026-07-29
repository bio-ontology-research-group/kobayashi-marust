#!/bin/bash
#SBATCH --job-name=km-v01-target
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --array=0-13%14
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-v01-d2aa211/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-v01-d2aa211
driver=/ibex/scratch/hohndor/km/auto-panel-20260728/driver
binary=$root/build/bin/km
km_root=/ibex/scratch/hohndor/km
run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
out=$root/targeted/$run_id
task=$root/work/$run_id/task-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
jdk=$km_root/bench/jdk8u492-b09
routes=(auto auto-speed auto-memory)
ontologies=(
    ore_ont_15672.owl ore_ont_1579.owl ore_ont_15846.owl
    ore_ont_5107.owl ore_ont_9654.owl
    ore_ont_10073.owl ore_ont_11315.owl ore_ont_11745.owl
    ore_ont_16462.owl ore_ont_4755.owl ore_ont_6223.owl
    ore_ont_7409.owl ore_ont_9400.owl ore_ont_9499.owl
)

export HOME=/home/hohndor
export PATH=$jdk/bin:/usr/bin:/bin
export LC_ALL=C
export RAYON_NUM_THREADS=16
export TMPDIR=$task/tmp
/usr/bin/mkdir -p "$task/tmp" "$out/results" "$out/failures"
binary_sha=$(/usr/bin/sha256sum "$binary" | /usr/bin/awk '{print $1}')

ontology=${ontologies[$SLURM_ARRAY_TASK_ID]}
source=$km_root/corpus/$ontology
gold=$km_root/gold/konclude__${ontology}.sig.gz
tmp=$out/results/$ontology.tmp.$SLURM_JOB_ID
: >"$tmp"
order=0
for route in "${routes[@]}"; do
    arm=km_route_${route//-/_}
    work=$task/$ontology/$arm
    /usr/bin/mkdir -p "$work"
    /usr/bin/python3 "$driver/full_panel_run_one.py" \
        --kind km --arm "$arm" --ontology "$source" \
        --binary "$binary" --binary-sha "$binary_sha" \
        --workdir "$work" --failures-dir "$out/failures/$ontology" \
        --checkpoint "$work/checkpoint.jsonl" --order-index "$order" \
        --timeout 300 --memcap-mb 30720 --gold-kind konclude \
        --gold "$gold" --env "KM_ROUTE=$route" >>"$tmp"
    order=$((order + 1))
done
/usr/bin/mv "$tmp" "$out/results/$ontology.jsonl"
/usr/bin/rm -rf "$task/$ontology"
echo "V01_TARGET_COMPLETE ontology=$ontology"
