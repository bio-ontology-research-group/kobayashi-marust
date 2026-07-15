#!/bin/bash
#SBATCH --job-name=km-14817-collect
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:02:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --output=/home/hohndor/bench/14817-collect-%j.out

set -u

root=/ibex/scratch/hohndor/km/14817_closure_20260714

for family in konclude-cache-ab coupling-split; do
  echo "FAMILY $family"
  find "$root/$family" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' 2>/dev/null | sort | while read -r variant; do
    run="$root/$family/$variant"
    echo "VARIANT $variant"
    if [[ -f "$run/14817.time" ]]; then
      grep -E 'Command exited|Elapsed \(wall clock\)|Percent of CPU|Maximum resident set size' "$run/14817.time" || true
    fi
    if [[ -f "$run/14817.stdout" ]]; then
      grep -E 'Finished (precomputing|class classification)|Total processing time' "$run/14817.stdout" || true
    fi
    if [[ -f "$run/14817.stderr" ]]; then
      grep -E '^(BRIDGE-(SATURATION|DEFER|PREPARE|VERIFY|KPSET|CLASSIFY)|PROGRESS-SAT)' "$run/14817.stderr" | tail -n 30 || true
    fi
    if [[ -f "$run/14817.json" ]]; then
      stat -c 'json-bytes=%s' "$run/14817.json"
    fi
  done
done

echo "SLURM"
find "$root/slurm" -maxdepth 1 -type f \
  \( -name 'konclude-cache-ab-48811712_*.out' -o -name 'coupling-split-48811806_*.out' \) \
  -print -exec cat {} \; 2>/dev/null | tail -n 400

trace="$root/konclude-nbo0042/14817.stderr"
echo "KCOMP-COUNTS"
if [[ -f "$trace" ]]; then
  for key in activate root-saturation root-initialized task-fixpoint successor-expansion-begin successor-expansion-end cache-establish some-attempt some-result; do
    printf '%s=' "$key"
    grep -c "KCOMP.*$key" "$trace" || true
  done
  echo "KCOMP-KEY-FIRST"
  grep -E 'KCOMP.*(activate|root-saturation|root-initialized|task-fixpoint|successor-expansion-(begin|end)|cache-establish|some-(attempt|result))' "$trace" | head -n 120 || true
  echo "KCOMP-KEY-LAST"
  grep -E 'KCOMP.*(activate|root-saturation|root-initialized|task-fixpoint|successor-expansion-(begin|end)|cache-establish|some-(attempt|result))' "$trace" | tail -n 120 || true
fi
