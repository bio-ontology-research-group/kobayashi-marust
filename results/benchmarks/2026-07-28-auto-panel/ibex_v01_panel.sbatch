#!/bin/bash
#SBATCH --job-name=km-v01-auto
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=1-00:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --array=0-29%30
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-v01-d2aa211/slurm-full-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-v01-d2aa211
driver=/ibex/scratch/hohndor/km/auto-panel-20260728/driver
binary=$root/build/bin/km
km_root=/ibex/scratch/hohndor/km
run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
out=$root/runs/$run_id
task=$root/work/$run_id/task-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
jdk=$km_root/bench/jdk8u492-b09
routes=(auto auto-speed auto-memory)

export HOME=/home/hohndor
export PATH=$jdk/bin:/usr/bin:/bin
export LC_ALL=C
export RAYON_NUM_THREADS=16
export TMPDIR=$task/tmp
/usr/bin/mkdir -p "$task/tmp" "$out/results" "$out/failures"
binary_sha=$(/usr/bin/sha256sum "$binary" | /usr/bin/awk '{print $1}')

mapfile -t indices < <(/usr/bin/python3 "$driver/full_panel_chunks.py" --total 592 --chunks 30 --chunk "$SLURM_ARRAY_TASK_ID")
for index in "${indices[@]}"; do
    ontology=$(/usr/bin/sed -n "$((index + 1))p" "$km_root/routing_20260715/onts.txt")
    source=$km_root/corpus/$ontology
    gold=$km_root/gold/konclude__${ontology}.sig.gz
    runner=$driver/full_panel_run_one.py
    case $ontology in ore_ont_3524.owl|ore_ont_15703.owl) runner=$driver/full_panel_run_one_fulliri_only.py ;; esac
    tmp=$out/results/$ontology.tmp.$SLURM_JOB_ID
    : >"$tmp"
    order=0
    for route in "${routes[@]}"; do
        arm=km_route_${route//-/_}
        work=$task/$ontology/$arm
        /usr/bin/mkdir -p "$work"
        /usr/bin/python3 "$runner" \
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
done
echo "V01_CHUNK_COMPLETE chunk=$SLURM_ARRAY_TASK_ID ontologies=${#indices[@]}"
