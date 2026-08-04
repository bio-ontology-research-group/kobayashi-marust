#!/bin/bash
#SBATCH --job-name=km-compact-ids-9674
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/compact-taxonomy-ids-20260804/pair-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/compact-taxonomy-ids-20260804
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_9674.owl
baseline=/ibex/scratch/hohndor/km/release-abe2759-auto-20260804/km
candidate=$root/km-candidate
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == 94077acb317cd5bafbd47d0ddce3ef1d693b52ba8998f1418df5d4247e05155e ]]
[[ -s $root/km-candidate.sha256 ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $(cut -d' ' -f1 < "$root/km-candidate.sha256") ]]

run_one() {
    local arm=$1 binary=$2 repetition=$3
    local receipt=$root/${arm}-${repetition}.time digest=$root/${arm}-${repetition}.sha256
    local output=${SLURM_TMPDIR:-/tmp}/${arm}-${repetition}-${SLURM_JOB_ID}.json
    : > "$receipt"
    /usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' -o "$receipt" \
        env -i PATH=/usr/bin:/bin HOME="$HOME" KM_ROUTE=auto \
        "$binary" classify "$ontology" > "$output"
    sha256sum "$output" | sed 's#  .*#  -#' > "$digest"
    rm "$output"
    grep -Eq '^elapsed=[0-9.]+ peak_kb=[0-9]+ exit=0$' "$receipt"
    grep -Eq '^[0-9a-f]{64}  -$' "$digest"
    printf '%s\trep=%s\t%s\tsha256=%s\n' "$arm" "$repetition" \
        "$(cat "$receipt")" "$(cut -d' ' -f1 < "$digest")"
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
