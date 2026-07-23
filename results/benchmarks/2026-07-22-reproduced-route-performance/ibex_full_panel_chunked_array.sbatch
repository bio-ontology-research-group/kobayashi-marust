#!/bin/bash
# Exactly 30 Slurm array tasks. Each task runs one balanced ORE ontology chunk.
#SBATCH --job-name=km-ore-panel30
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=7-00:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-29%30
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260723-rerun/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "panel chunk failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_full_panel_clean_environment_v2__
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
[[ $SLURM_ARRAY_TASK_ID =~ ^([0-9]|[12][0-9])$ ]]
[[ $PANEL_RUN_ID =~ ^[0-9]+$ ]]

km_root=/ibex/scratch/hohndor/km
root=$km_root/full-panel-20260723-rerun
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
fulliri_runner=$driver_dir/full_panel_run_one_fulliri_only.py
fingerprint=$driver_dir/full_panel_fingerprint.py
orchestrator=$driver_dir/run_full_panel_ontology.py
chunker=$driver_dir/full_panel_chunks.py
rustdl_adapter=$driver_dir/rustdl_json_adapter.py
sequoia_adapter=$driver_dir/sequoia_json_adapter.py
ontology_list=$km_root/routing_20260715/onts.txt
konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03

for required in \
    "$driver_dir/full_panel_contract.py" "$driver_dir/full_panel_correctness.py" \
    "$base_runner" "$fulliri_runner" "$fingerprint" "$orchestrator" "$chunker" \
    "$rustdl_adapter" "$sequoia_adapter" "$driver_dir/ore_canon.py" \
    "$driver_dir/tree_watchdog.py" "$build_root/build-receipt.json" \
    "$build_root/bin/km-main" "$build_root/bin/rustdl" "$build_root/bin/sequoia" \
    "$konclude_root/Konclude-build-a" "$konclude_root/runtime-files.sha256" \
    "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    "$build_root/bin/FullIriHermitOracle.class" "$jdk/bin/java" "$ontology_list"
do
    [[ -s $required ]] || { echo "missing benchmark input: $required" >&2; exit 2; }
done
[[ -d $konclude_root/runtime-lib ]]

result_root=$root/runs/$PANEL_RUN_ID
work_root=$root/work/$PANEL_RUN_ID
task_tmp=$work_root/tmp-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"
export TMPDIR=$task_tmp

mapfile -t ontology_indices < <(
    /usr/bin/python3 "$chunker" \
        --total 592 \
        --chunks 30 \
        --chunk "$SLURM_ARRAY_TASK_ID"
)
expected_size=19
if (( SLURM_ARRAY_TASK_ID < 22 )); then
    expected_size=20
fi
[[ ${#ontology_indices[@]} -eq $expected_size ]]

failures=0
for ontology_index in "${ontology_indices[@]}"; do
    ontology=$(/usr/bin/sed -n "$((ontology_index + 1))p" "$ontology_list")
    runner=$base_runner
    case $ontology in
        ore_ont_3524.owl|ore_ont_15703.owl) runner=$fulliri_runner ;;
    esac
    export PANEL_ONTOLOGY_INDEX=$ontology_index
    echo "PANEL_CHUNK ontology_index=$ontology_index ontology=$ontology runner=$runner"
    if ! /usr/bin/python3 "$orchestrator" \
        --task-index "$ontology_index" \
        --ontology-list "$ontology_list" \
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
    then
        failures=$((failures + 1))
        echo "ONTOLOGY_FAILED ontology_index=$ontology_index ontology=$ontology" >&2
    fi
done

if (( failures != 0 )); then
    echo "CHUNK_INCOMPLETE chunk=$SLURM_ARRAY_TASK_ID failures=$failures" >&2
    exit 1
fi
echo "CHUNK_COMPLETE chunk=$SLURM_ARRAY_TASK_ID ontologies=${#ontology_indices[@]}"
