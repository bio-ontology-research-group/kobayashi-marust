#!/bin/bash
#SBATCH --job-name=km-ht-reuse-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --array=0-69%10
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:12:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/ht-model-reuse-20260805/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/ht-model-reuse-20260805
binary=/ibex/scratch/hohndor/km/release-9ee269e-auto-20260804/km
list=$root/ontologies.txt
ontology=$(sed -n "$((SLURM_ARRAY_TASK_ID + 1))p" "$list")
input=/ibex/scratch/hohndor/km/corpus/$ontology
expected_binary=be326fe76e9cbe52d574ad8d5f3c037ae3db9f9fd3d25b498a1f90492534a6dd
[[ -n $ontology && -f $input ]]
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]

run_one() {
    local arm=$1
    shift
    local output=${SLURM_TMPDIR:-/tmp}/${arm}-${SLURM_ARRAY_TASK_ID}.json
    local receipt=$root/${ontology}.${arm}.time
    local digest=$root/${ontology}.${arm}.sha256
    : > "$receipt"
    /usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' -o "$receipt" \
        timeout --signal=TERM --kill-after=10s 260s \
        env -i PATH=/usr/bin:/bin HOME="$HOME" KM_ROUTE=auto "$@" \
        "$binary" classify "$input" > "$output" 2> "$root/${ontology}.${arm}.stderr"
    sha256sum "$output" | sed 's#  .*#  -#' > "$digest"
    grep -Eq '^elapsed=[0-9.]+ peak_kb=[0-9]+ exit=0$' "$receipt"
    grep -Eq '^[0-9a-f]{64}  -$' "$digest"
    printf '%s\t%s\t%s\tsha256=%s\n' "$ontology" "$arm" \
        "$(cat "$receipt")" "$(cut -d' ' -f1 < "$digest")"
}

run_one baseline
run_one reuse KM_HT_WITREUSE=1 KM_HT_MODELPRUNE=1
cmp "$root/${ontology}.baseline.sha256" "$root/${ontology}.reuse.sha256"
echo "TASK_COMPLETE ontology=$ontology"
