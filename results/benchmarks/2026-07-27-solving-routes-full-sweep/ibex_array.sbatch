#!/bin/bash
# Fifty balanced pooled jobs; each ontology runs the frozen 47-procedure panel.
#SBATCH --job-name=km-routes47
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=7-00:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-49%50
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes/slurm-%x-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes
driver_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?}")
build_root=$root/build
km_root=/ibex/scratch/hohndor/km
jdk=$km_root/bench/jdk8u492-b09
export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C PYTHONHASHSEED=0 RAYON_NUM_THREADS=16
[[ $SLURM_ARRAY_TASK_ID =~ ^([0-9]|[1-4][0-9])$ ]]
run_id=${PANEL_RUN_ID:-$SLURM_ARRAY_JOB_ID}
result_root=$root/runs/$run_id
work_root=$root/work/$run_id
task_tmp=$work_root/tmp-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"
export TMPDIR=$task_tmp

ontology_list=$km_root/routing_20260715/onts.txt
konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
mapfile -t indices < <(/usr/bin/python3 "$driver_dir/full_panel_chunks.py" \
  --total 592 --chunks 50 --chunk "$SLURM_ARRAY_TASK_ID")
expected=11
(( SLURM_ARRAY_TASK_ID < 42 )) && expected=12
[[ ${#indices[@]} -eq $expected ]]

failures=0
for index in "${indices[@]}"; do
  ontology=$(/usr/bin/sed -n "$((index + 1))p" "$ontology_list")
  runner=$driver_dir/full_panel_run_one.py
  case $ontology in ore_ont_3524.owl|ore_ont_15703.owl)
    runner=$driver_dir/full_panel_run_one_fulliri_only.py ;; esac
  export PANEL_ONTOLOGY_INDEX=$index
  if ! /usr/bin/python3 "$driver_dir/run_full_panel_ontology.py" \
    --task-index "$index" --ontology-list "$ontology_list" \
    --corpus "$km_root/corpus" --gold "$km_root/gold" \
    --build-root "$build_root" --benchmark-root "$km_root/bench" \
    --result-root "$result_root" --work-root "$work_root" \
    --runner "$runner" --fingerprint "$driver_dir/full_panel_fingerprint.py" \
    --rustdl-adapter "$build_root/bin/rustdl" \
    --sequoia-adapter "$build_root/bin/sequoia" \
    --konclude "$konclude_root/Konclude-build-a" \
    --konclude-library "$konclude_root/runtime-lib" \
    --konclude-runtime-manifest "$konclude_root/runtime-files.sha256" \
    --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    --hermit-oracle "$build_root/bin/FullIriHermitOracle.class" \
    --hermit-classpath "$build_root/bin:$km_root/bench/hermit_cp/*" \
    --java "$jdk/bin/java" --timeout 240 --memcap-mb 20480
  then failures=$((failures + 1)); fi
done
(( failures == 0 )) || { echo "CHUNK_INCOMPLETE failures=$failures" >&2; exit 1; }
echo "CHUNK_COMPLETE chunk=$SLURM_ARRAY_TASK_ID ontologies=${#indices[@]}"
