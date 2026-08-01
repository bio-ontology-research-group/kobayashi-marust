#!/bin/bash
# One ontology per task; each task runs all 55 current-release procedures.
#SBATCH --job-name=km-v020-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-591%32
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/release-v020-uniform-20260801/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; printf "PANEL_TASK_FAILED line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

root=/ibex/scratch/hohndor/km/release-v020-uniform-20260801
drivers=$root/drivers
build=$root/build
km_root=/ibex/scratch/hohndor/km
jdk=$km_root/bench/jdk8u492-b09
konclude=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
run_id=$SLURM_ARRAY_JOB_ID
result_root=$root/runs/$run_id
work_root=$root/work/$run_id
task_tmp=${SLURM_TMPDIR:-$root/tmp-$SLURM_JOB_ID}/km-panel-$SLURM_ARRAY_TASK_ID

export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
export RAYON_NUM_THREADS=16
export TMPDIR=$task_tmp
umask 0027
/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"

for required in \
    "$drivers/full_panel_contract.py" \
    "$drivers/_frozen_contract_20260722.py" \
    "$drivers/full_panel_run_one.py" \
    "$drivers/full_panel_fingerprint.py" \
    "$drivers/run_full_panel_ontology.py" \
    "$drivers/rustdl_json_adapter.py" \
    "$drivers/sequoia_json_adapter.py" \
    "$drivers/ore_canon.py" \
    "$drivers/tree_watchdog.py" \
    "$build/build-receipt.json" \
    "$build/bin/km-main" \
    "$build/bin/rustdl" \
    "$build/bin/sequoia" \
    "$build/bin/FullIriHermitOracle.class" \
    "$konclude/Konclude-build-a" \
    "$konclude/runtime-files.sha256" \
    "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    "$jdk/bin/java"
do
    [[ -e $required ]] || { echo "missing benchmark input: $required" >&2; exit 2; }
done

/usr/bin/python3 "$drivers/run_full_panel_ontology.py" \
    --task-index "$SLURM_ARRAY_TASK_ID" \
    --ontology-list "$km_root/routing_20260715/onts.txt" \
    --corpus "$km_root/corpus" \
    --gold "$km_root/gold" \
    --build-root "$build" \
    --benchmark-root "$km_root/bench" \
    --result-root "$result_root" \
    --work-root "$work_root" \
    --runner "$drivers/full_panel_run_one.py" \
    --fingerprint "$drivers/full_panel_fingerprint.py" \
    --rustdl-adapter "$drivers/rustdl_json_adapter.py" \
    --sequoia-adapter "$drivers/sequoia_json_adapter.py" \
    --konclude "$konclude/Konclude-build-a" \
    --konclude-library "$konclude/runtime-lib" \
    --konclude-runtime-manifest "$konclude/runtime-files.sha256" \
    --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    --hermit-oracle "$build/bin/FullIriHermitOracle.class" \
    --hermit-classpath "$build/bin:$km_root/bench/hermit_cp/*" \
    --java "$jdk/bin/java" \
    --timeout 240 \
    --memcap-mb 20480

echo "PANEL_TASK_COMPLETE ontology_index=$SLURM_ARRAY_TASK_ID run=$run_id"
