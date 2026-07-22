#!/bin/bash
# Supplemental tasks for the two ontologies with non-injective local names.
#SBATCH --job-name=km-ore-panel-fulliri
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=121,552%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260722/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "panel task failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_full_panel_giant_clean_environment_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    panel_run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_ARRAY_JOB_ID="${SLURM_ARRAY_JOB_ID:?missing Slurm array identifier}" \
        SLURM_ARRAY_TASK_ID="${SLURM_ARRAY_TASK_ID:?missing Slurm task identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        PANEL_RUN_ID="$panel_run_id" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
[[ $SLURM_CPUS_PER_TASK == 16 ]]
[[ $PANEL_RUN_ID =~ ^[0-9]+$ ]]
case "$SLURM_ARRAY_TASK_ID" in
    121|552) ;;
    *) echo "invalid supplemental task index: $SLURM_ARRAY_TASK_ID" >&2; exit 2 ;;
esac

km_root=/ibex/scratch/hohndor/km
root=$km_root/full-panel-20260722
build_root=$root/build
driver_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
jdk=$km_root/bench/jdk8u492-b09
export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
export RAYON_NUM_THREADS=16
umask 0027

base_runner=$driver_dir/full_panel_run_one.py
runner=$driver_dir/full_panel_run_one_fulliri_only.py
fingerprint=$driver_dir/full_panel_fingerprint.py
orchestrator=$driver_dir/run_full_panel_ontology.py
rustdl_adapter=$driver_dir/rustdl_json_adapter.py
sequoia_adapter=$driver_dir/sequoia_json_adapter.py
konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03

for required in \
    "$driver_dir/full_panel_contract.py" "$base_runner" "$runner" \
    "$fingerprint" "$orchestrator" "$rustdl_adapter" "$sequoia_adapter" \
    "$driver_dir/ore_canon.py" "$driver_dir/tree_watchdog.py" \
    "$build_root/build-receipt.json" "$build_root/bin/km-main" \
    "$build_root/bin/rustdl" "$build_root/bin/sequoia" \
    "$konclude_root/Konclude-build-a" "$konclude_root/runtime-files.sha256" \
    "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    "$build_root/bin/FullIriHermitOracle.class" "$jdk/bin/java"
do
    [[ -s $required ]] || { echo "missing benchmark input: $required" >&2; exit 2; }
done
[[ -d $konclude_root/runtime-lib ]]

result_root=$root/runs/$PANEL_RUN_ID
work_root=$root/work/$PANEL_RUN_ID
task_tmp=$work_root/tmp-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"
export TMPDIR=$task_tmp

/usr/bin/python3 "$orchestrator" \
    --task-index "$SLURM_ARRAY_TASK_ID" \
    --ontology-list "$km_root/routing_20260715/onts.txt" \
    --corpus "$km_root/corpus" \
    --gold "$km_root/gold" \
    --build-root "$build_root" \
    --benchmark-root "$km_root/bench" \
    --result-root "$result_root" \
    --work-root "$work_root" \
    --runner "$runner" \
    --fingerprint "$fingerprint" \
    --rustdl-adapter "$rustdl_adapter" \
    --sequoia-adapter "$sequoia_adapter" \
    --konclude "$konclude_root/Konclude-build-a" \
    --konclude-library "$konclude_root/runtime-lib" \
    --konclude-runtime-manifest "$konclude_root/runtime-files.sha256" \
    --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    --hermit-oracle "$build_root/bin/FullIriHermitOracle.class" \
    --hermit-classpath "$build_root/bin:$km_root/bench/hermit_cp/*" \
    --java "$jdk/bin/java" \
    --timeout 240 \
    --memcap-mb 20480
