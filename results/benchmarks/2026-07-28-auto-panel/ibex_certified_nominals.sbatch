#!/bin/bash
#SBATCH --job-name=km-certified-nominals
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --array=0-24%25
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-panel-20260728/certified-nominals/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-panel-20260728
driver=$root/driver
binary=$root/build/bin/km-main
km_root=/ibex/scratch/hohndor/km
out_root=$root/certified-nominals
jdk=$km_root/bench/jdk8u492-b09
ids=(10702 10860 10908 1194 12653 13503 1481 15516 15672 1579 15803 15846 2669 3377 3560 4669 5107 541 6477 6934 6999 7499 7914 9635 9654)
routes=(certified_nominals certified_card_nominals)
id=${ids[$SLURM_ARRAY_TASK_ID]}
ontology=ore_ont_${id}.owl
source=$km_root/corpus/$ontology
gold=$km_root/gold/konclude__${ontology}.sig.gz
task=$out_root/task-$SLURM_JOB_ID-$id
result=$out_root/results/$ontology.jsonl

export HOME=/home/hohndor
export PATH=$jdk/bin:/usr/bin:/bin
export LC_ALL=C
export RAYON_NUM_THREADS=16
export TMPDIR=$task/tmp
/usr/bin/mkdir -p "$task/tmp" "$out_root/results" "$out_root/failures/$ontology"
binary_sha=$(/usr/bin/sha256sum "$binary" | /usr/bin/awk '{print $1}')
tmp=$result.tmp.$SLURM_JOB_ID
: >"$tmp"
order=0
for route in "${routes[@]}"; do
    arm=km_route_$route
    arm_work=$task/$arm
    /usr/bin/mkdir -p "$arm_work"
    /usr/bin/python3 "$driver/full_panel_run_one.py" \
        --kind km --arm "$arm" --ontology "$source" \
        --binary "$binary" --binary-sha "$binary_sha" \
        --workdir "$arm_work" \
        --failures-dir "$out_root/failures/$ontology" \
        --checkpoint "$arm_work/checkpoint.jsonl" \
        --order-index "$order" --timeout 300 --memcap-mb 30720 \
        --gold "$gold" --gold-kind konclude --env "KM_ROUTE=$route" \
        >>"$tmp"
    order=$((order + 1))
done
/usr/bin/mv "$tmp" "$result"
/usr/bin/rm -rf "$task"
echo "CERTIFIED_NOMINALS_COMPLETE ontology=$ontology"
