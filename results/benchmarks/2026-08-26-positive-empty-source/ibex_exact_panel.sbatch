#!/bin/bash
#SBATCH --job-name=km-v110-positive-empty-exact
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --array=0-25%6
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826/exact-panel/slurm-%A_%a.out

set -euo pipefail
v5_root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826
corpus=/ibex/scratch/hohndor/km/corpus
v5_hash=e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620
v7_hash=a28b41934ea033f8274b3a71734ea6733a3989d573e8eccd5ca099c08bd344b8
accepted=(1012 1306 2046 2253 4033 4557 5602 5760 6233 7993 9768 10750 13482 14216 15280)
controls=(33 105 148 1016 1017 7499 9014 9540 16821 3377 7246)
ids=("${accepted[@]}" "${controls[@]}")
id=${ids[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${id}.owl
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$v5_root/km" | cut -d' ' -f1) == "$v5_hash" ]]
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$v7_hash" ]]
work=${SLURM_TMPDIR:-/tmp}/km-v110-positive-panel-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$work" "$root/exact-panel/results"
trap 'rm -rf "$work"' EXIT

for arm in v5 v7_off v7_on; do
  case $arm in
    v5) bin=$v5_root/km; env_args=() ;;
    v7_off) bin=$root/km; env_args=() ;;
    v7_on) bin=$root/km; env_args=(KM_POSITIVE_EMPTY_SOURCE=1) ;;
  esac
  timeout -k 5 240 /usr/bin/time -f '%e %M %x' -o "$work/$arm.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "${env_args[@]}" "$bin" classify "$input" \
      > "$work/$arm.json" 2> "$work/$arm.stderr"
  read -r wall rss exit_code < "$work/$arm.measure"
  [[ $exit_code == 0 ]]
  echo "MEASURE ontology=$id arm=$arm wall=$wall rss_kib=$rss exit=$exit_code"
done

cmp "$work/v5.json" "$work/v7_off.json"
cmp "$work/v5.json" "$work/v7_on.json"
! grep -q 'route=positive_empty_source' "$work/v7_off.stderr"
if (( SLURM_ARRAY_TASK_ID < ${#accepted[@]} )); then
  grep -q 'route=positive_empty_source' "$work/v7_on.stderr"
  expected_route=positive_empty_source
else
  ! grep -q 'route=positive_empty_source' "$work/v7_on.stderr"
  expected_route=unchanged-control
fi
sha256sum "$work/v7_on.json"
for arm in v5 v7_off v7_on; do
  install -m 644 "$work/$arm.measure" "$root/exact-panel/results/${id}.${arm}.measure"
done
install -m 644 "$work/v7_on.stderr" "$root/exact-panel/results/${id}.v7_on.stderr"
echo "EXACT_TRIPLE ontology=$id route=$expected_route"
