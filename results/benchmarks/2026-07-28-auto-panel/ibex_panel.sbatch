#!/bin/bash
#SBATCH --job-name=km-auto-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=2-00:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --array=0-29%30
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-panel-20260728/slurm-%x-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/auto-panel-20260728
driver_dir=$root/driver
build_root=$root/build
km_root=/ibex/scratch/hohndor/km
run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
result_root=$root/runs/$run_id
work_root=$root/work/$run_id
task_tmp=$work_root/tmp-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
jdk=$km_root/bench/jdk8u492-b09
konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03

export HOME=/home/hohndor
export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
export RAYON_NUM_THREADS=16
export TMPDIR=$task_tmp
umask 0027

/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"
mapfile -t ontology_indices < <(
    /usr/bin/python3 "$driver_dir/full_panel_chunks.py" \
        --total 592 --chunks 30 --chunk "$SLURM_ARRAY_TASK_ID"
)

failures=0
for ontology_index in "${ontology_indices[@]}"; do
    ontology=$(/usr/bin/sed -n "$((ontology_index + 1))p" "$km_root/routing_20260715/onts.txt")
    runner=$driver_dir/full_panel_run_one.py
    case $ontology in
        ore_ont_3524.owl|ore_ont_15703.owl) runner=$driver_dir/full_panel_run_one_fulliri_only.py ;;
    esac
    if ! /usr/bin/python3 "$driver_dir/run_full_panel_ontology.py" \
        --task-index "$ontology_index" \
        --ontology-list "$km_root/routing_20260715/onts.txt" \
        --corpus "$km_root/corpus" \
        --gold "$km_root/gold" \
        --build-root "$build_root" \
        --benchmark-root "$km_root/bench" \
        --result-root "$result_root" \
        --work-root "$work_root" \
        --runner "$runner" \
        --fingerprint "$driver_dir/full_panel_fingerprint.py" \
        --rustdl-adapter "$driver_dir/rustdl_json_adapter.py" \
        --sequoia-adapter "$driver_dir/sequoia_json_adapter.py" \
        --konclude "$konclude_root/Konclude-build-a" \
        --konclude-library "$konclude_root/runtime-lib" \
        --konclude-runtime-manifest "$konclude_root/runtime-files.sha256" \
        --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
        --hermit-oracle "$build_root/bin/FullIriHermitOracle.class" \
        --hermit-classpath "$build_root/bin:$km_root/bench/hermit_cp/*" \
        --java "$jdk/bin/java" \
        --timeout 300 \
        --memcap-mb 30720
    then
        failures=$((failures + 1))
        echo "ONTOLOGY_FAILED index=$ontology_index ontology=$ontology" >&2
    fi
done

(( failures == 0 )) || { echo "CHUNK_INCOMPLETE failures=$failures" >&2; exit 1; }
echo "CHUNK_COMPLETE chunk=$SLURM_ARRAY_TASK_ID ontologies=${#ontology_indices[@]}"
