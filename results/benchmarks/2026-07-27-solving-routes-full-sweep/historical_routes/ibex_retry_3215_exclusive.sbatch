#!/bin/bash
# Recheck the narrow-margin historical 3215 route without node contention.
#SBATCH --job-name=km-3215-historical-exclusive
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes
driver_dir=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes/drivers-historical-50c69f9
km_root=/ibex/scratch/hohndor/km
build_root=$root/build
jdk=$km_root/bench/jdk8u492-b09
ontology_list=$km_root/routing_20260715/onts.txt
konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
index=$(( $(/usr/bin/grep -n '^ore_ont_3215.owl$' "$ontology_list" | /usr/bin/cut -d: -f1) - 1 ))
export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C PYTHONHASHSEED=0 RAYON_NUM_THREADS=16
export PANEL_ONTOLOGY_INDEX=$index
result_root=$root/runs/$SLURM_JOB_ID
work_root=$root/work/$SLURM_JOB_ID
/usr/bin/mkdir -p "$result_root" "$work_root"

/usr/bin/python3 "$driver_dir/run_full_panel_ontology.py" \
  --task-index "$index" --ontology-list "$ontology_list" \
  --corpus "$km_root/corpus" --gold "$km_root/gold" \
  --build-root "$build_root" --benchmark-root "$km_root/bench" \
  --result-root "$result_root" --work-root "$work_root" \
  --runner "$driver_dir/full_panel_run_one.py" \
  --fingerprint "$driver_dir/full_panel_fingerprint.py" \
  --rustdl-adapter "$build_root/bin/rustdl" \
  --sequoia-adapter "$build_root/bin/sequoia" \
  --konclude "$konclude_root/Konclude-build-a" \
  --konclude-library "$konclude_root/runtime-lib" \
  --konclude-runtime-manifest "$konclude_root/runtime-files.sha256" \
  --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
  --hermit-oracle "$build_root/bin/FullIriHermitOracle.class" \
  --hermit-classpath "$build_root/bin:$km_root/bench/hermit_cp/*" \
  --java "$jdk/bin/java" --timeout 240 --memcap-mb 20480
