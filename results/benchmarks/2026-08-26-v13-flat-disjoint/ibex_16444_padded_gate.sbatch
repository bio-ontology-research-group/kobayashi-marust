#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:06:00
#SBATCH --output=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/padded-16444-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826
binary=$root/km
expected=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
input=/ibex/scratch/hohndor/km/corpus/ore_ont_16444.owl
work=${SLURM_TMPDIR:-/tmp}/km-v13-padded-16444-${SLURM_JOB_ID}
mkdir -p "$work" "$root/padded-16444"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
cp "$input" "$work/padded.owl"
# Raise only the source-size routing signal with semantically inert blank lines.
head -c $((9 * 1024 * 1024)) /dev/zero | tr '\0' '\n' >> "$work/padded.owl"
(( $(stat -c %s "$work/padded.owl") >= 32 * 1024 * 1024 ))

for arm in original padded; do
  source=$input
  [[ $arm == padded ]] && source=$work/padded.owl
  timeout -k 5 240 /usr/bin/time -f '%e %M %x' -o "$work/$arm.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$source" \
      > "$work/$arm.json" 2> "$work/$arm.stderr"
  read -r wall rss rc < "$work/$arm.measure"
  [[ $rc == 0 && -s "$work/$arm.json" ]]
  printf 'RESULT arm=%s wall_s=%s rss_kib=%s\n' "$arm" "$wall" "$rss"
done
grep -q 'route=flat_nf1' "$work/padded.stderr"
cmp "$work/original.json" "$work/padded.json"
install -m 644 "$work/padded.stderr" "$root/padded-16444/padded.stderr"
install -m 644 "$work/original.measure" "$root/padded-16444/original.measure"
install -m 644 "$work/padded.measure" "$root/padded-16444/padded.measure"
echo EXACT_PADDED_ROUTE
