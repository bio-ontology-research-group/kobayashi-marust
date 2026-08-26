#!/bin/bash
#SBATCH --job-name=km-v110-v6-abox-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --array=0-21%6
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v6-20260826/panel/slurm-%A_%a.out

set -euo pipefail

v5_root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v6-20260826
corpus=/ibex/scratch/hohndor/km/corpus
v5_hash=e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620
v6_hash=f4e53b0946a4a9b76ef2b115f52dd65f8b23f5b285a7691a3c7cf85b10c86c85
ids=(1012 1306 2046 2253 3164 3658 4187 4557 5519 5602 5760 6233 7993 9768 9958 10750 12528 13482 14216 15280 9499 10073)
id=${ids[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${id}.owl
work=${SLURM_TMPDIR:-/tmp/km-v110-v6-panel-${SLURM_JOB_ID}}
mkdir -p "$work" "$root/panel/results"
trap 'rm -rf "$work"' EXIT

[[ $(sha256sum "$v5_root/km" | cut -d' ' -f1) == "$v5_hash" ]]
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$v6_hash" ]]
for arm in v5 v6; do
  if [[ $arm == v5 ]]; then bin=$v5_root/km; else bin=$root/km; fi
  timeout 240 /usr/bin/time -f '%e %M %x' -o "$work/$arm.measure" \
    env KM_ROUTE=auto "$bin" classify "$input" > "$work/$arm.json"
  read -r wall rss exit_code < "$work/$arm.measure"
  echo "MEASURE ontology=$id arm=$arm wall=$wall rss_kib=$rss exit=$exit_code"
  [[ $exit_code == 0 ]]
done
cmp "$work/v5.json" "$work/v6.json"
sha256sum "$work/v6.json"
install -m 644 "$work/v5.measure" "$root/panel/results/${id}.v5.measure"
install -m 644 "$work/v6.measure" "$root/panel/results/${id}.v6.measure"
echo "EXACT_PAIR ontology=$id"
