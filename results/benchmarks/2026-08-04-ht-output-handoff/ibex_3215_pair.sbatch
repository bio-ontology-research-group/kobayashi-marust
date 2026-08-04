#!/bin/bash
#SBATCH --job-name=km-ht-handoff-3215
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/ht-output-handoff-20260804/pair-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/ht-output-handoff-20260804
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl
baseline=/ibex/scratch/hohndor/km/release-9ee269e-auto-20260804/km
candidate=$root/km-candidate
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == be326fe76e9cbe52d574ad8d5f3c037ae3db9f9fd3d25b498a1f90492534a6dd ]]
[[ -s $root/km-candidate.sha256 ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $(cut -d' ' -f1 < "$root/km-candidate.sha256") ]]

run_one() {
    local arm=$1 binary=$2 repetition=$3
    local receipt=$root/${arm}-${repetition}.time digest=$root/${arm}-${repetition}.sha256
    local trace=$root/${arm}-${repetition}.trace
    local output=${SLURM_TMPDIR:-/tmp}/${arm}-${repetition}-${SLURM_JOB_ID}.json
    : > "$receipt"
    : > "$trace"
    /usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' -o "$receipt" \
        env -i PATH=/usr/bin:/bin HOME="$HOME" KM_ROUTE=auto KM_TIMING=1 \
        "$binary" classify "$ontology" > "$output" 2> "$trace"
    sha256sum "$output" | sed 's#  .*#  -#' > "$digest"
    rm "$output"
    grep -Eq '^elapsed=[0-9.]+ peak_kb=[0-9]+ exit=0$' "$receipt"
    grep -q 'KM_TIMING race: read_tout done' "$trace"
    grep -Eq '^[0-9a-f]{64}  -$' "$digest"
    printf '%s\trep=%s\t%s\tsha256=%s\n' "$arm" "$repetition" \
        "$(cat "$receipt")" "$(cut -d' ' -f1 < "$digest")"
    grep 'KM_TIMING' "$trace"
}
for repetition in 1 2 3; do
    run_one baseline "$baseline" "$repetition"
    run_one candidate "$candidate" "$repetition"
done
expected=$(cut -d' ' -f1 < "$root/baseline-1.sha256")
for arm in baseline candidate; do
    for repetition in 1 2 3; do
        [[ $(cut -d' ' -f1 < "$root/${arm}-${repetition}.sha256") == "$expected" ]]
    done
done
echo "BENCHMARK_COMPLETE output_sha256=$expected"
