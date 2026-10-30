#!/bin/bash
# Paired protocol runs: each input runs with KM_BIN_A and KM_BIN_B in the same
# task (same node), order alternating by index. KM_TAGRUN, KM_LIST, KM_TASKS.
#SBATCH --job-name=km155-nc-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=04:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030/slurm/pair-%A_%a.out
set -uo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030
C=/ibex/scratch/hohndor/km/v143-harness-20260918/corpus/pool_sample/files
mapfile -t names < "$KM_LIST"
one() {  # one BIN TAG NAME
  local bin=$1 tag=$2 n=$3
  local out=$ROOT/out/$tag/$n; /usr/bin/mkdir -p "$out"
  export TMPDIR=$ROOT/tmp/${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}; /usr/bin/mkdir -p "$TMPDIR"
  local s=$(date +%s.%N)
  env KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_TIMING=1 /usr/bin/timeout -s KILL 240 "$bin" classify --lines "$C/$n.owl" > "$out/out.txt" 2> "$out/err.txt"
  local rc=$?; local e=$(date +%s.%N)
  grep -E '^(SUB|UNSAT|CONSISTENT)' "$out/out.txt" | sort | gzip > "$out/sig.gz"; rm -f "$out/out.txt"
  local rel=$(grep -c 'nominal CB input: released' "$out/err.txt"); tail -c 3000 "$out/err.txt" > "$out/errtail.txt"; rm -f "$out/err.txt"
  echo -e "$n\t$tag\t$rc\t$(echo "$e - $s" | bc)\t$(hostname)\t$rel" > "$out/time.tsv"
  /usr/bin/rm -rf "$TMPDIR"
}
for v in $(env | grep -o '^KM_[A-Z_0-9]*' | grep -v -E '^KM_(BIN_A|BIN_B|TAGRUN|LIST|TASKS)$'); do unset $v; done
for ((j=SLURM_ARRAY_TASK_ID; j<${#names[@]}; j+=KM_TASKS)); do
  n=${names[$j]}
  if (( j % 2 )); then one "$KM_BIN_A" "$KM_TAGRUN-A" "$n"; one "$KM_BIN_B" "$KM_TAGRUN-B" "$n";
  else one "$KM_BIN_B" "$KM_TAGRUN-B" "$n"; one "$KM_BIN_A" "$KM_TAGRUN-A" "$n"; fi
done
