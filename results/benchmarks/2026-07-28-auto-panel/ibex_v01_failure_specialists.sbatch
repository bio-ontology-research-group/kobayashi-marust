#!/bin/bash
# Current-v0.1 specialist audit over every non-accepted automatic-policy input.
#SBATCH --job-name=km-v01-fail-spec
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --array=0-16%17
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-v01-d2aa211/slurm-spec-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-v01-d2aa211
driver=/ibex/scratch/hohndor/km/auto-panel-20260728/driver
binary=$root/build/bin/km
km_root=/ibex/scratch/hohndor/km
run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
out=$root/failure-specialists/$run_id
task=$root/work/$run_id/task-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
jdk=$km_root/bench/jdk8u492-b09
ontologies=(
    ore_ont_541.owl ore_ont_1194.owl ore_ont_1481.owl
    ore_ont_3377.owl ore_ont_3560.owl ore_ont_4669.owl
    ore_ont_6477.owl ore_ont_6934.owl ore_ont_6999.owl
    ore_ont_7499.owl ore_ont_7914.owl ore_ont_9635.owl
    ore_ont_10702.owl ore_ont_10860.owl ore_ont_10908.owl
    ore_ont_12653.owl ore_ont_15803.owl
)
routes=(
    nominals elc_cert production_all ht_shoq ht_qo ht_card card_fn
    ht_features ht_general ht_rules tab_race
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
    arm=km_route_$route
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
echo "V01_FAILURE_SPECIALISTS_COMPLETE ontology=$ontology routes=${#routes[@]}"
