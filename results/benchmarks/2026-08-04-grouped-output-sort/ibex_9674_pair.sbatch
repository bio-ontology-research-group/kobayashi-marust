#!/bin/bash
#SBATCH --job-name=km-group-sort-9674
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/grouped-output-sort-20260804/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/grouped-output-sort-20260804
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_9674.owl
baseline=/ibex/scratch/hohndor/km/release-df5bb5b-auto-20260804/km
candidate=$root/km-candidate
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == 546ecedfd926794879e1ddae60cfd74e00896a264b0513324afaef0060161089 ]]
[[ -s $root/km-candidate.sha256 ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $(cut -d' ' -f1 < "$root/km-candidate.sha256") ]]

run_one() {
    local arm=$1
    local binary=$2
    local repetition=$3
    local receipt=$root/${arm}-${repetition}.time
    local digest=$root/${arm}-${repetition}.sha256
    : > "$receipt"
    {
        /usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' -o "$receipt" \
            env -i PATH=/usr/bin:/bin HOME="$HOME" KM_ROUTE=auto \
            "$binary" classify "$ontology"
    } | sha256sum > "$digest"
    grep -Eq '^elapsed=[0-9.]+ peak_kb=[0-9]+ exit=0$' "$receipt"
    grep -Eq '^[0-9a-f]{64}  -$' "$digest"
    printf '%s\trep=%s\t%s\tsha256=%s\n' \
        "$arm" "$repetition" "$(cat "$receipt")" "$(cut -d' ' -f1 < "$digest")"
}

for repetition in 1 2 3; do
    run_one baseline "$baseline" "$repetition"
    run_one candidate "$candidate" "$repetition"
done

baseline_hash=$(cut -d' ' -f1 < "$root/baseline-1.sha256")
candidate_hash=$(cut -d' ' -f1 < "$root/candidate-1.sha256")
[[ $baseline_hash == "$candidate_hash" ]]
for arm in baseline candidate; do
    for repetition in 2 3; do
        [[ $(cut -d' ' -f1 < "$root/${arm}-${repetition}.sha256") == "$baseline_hash" ]]
    done
done
echo "BENCHMARK_COMPLETE output_sha256=$baseline_hash"
