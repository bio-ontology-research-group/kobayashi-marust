#!/bin/bash
#SBATCH --job-name=km-v110-panel-v5
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825/panel-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
corpus=/ibex/scratch/hohndor/km/corpus
v036=/ibex/scratch/hohndor/km/v036-large-clean-20260815/km
candidate=$root/km
[[ $(sha256sum "$v036" | cut -d' ' -f1) == bbef8d7efbc6a6b8aefa3c44e55f40fb90916f1974d6c8086eb77bb7ac1d074f ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620 ]]
work=${SLURM_TMPDIR:-/tmp/km-v110-panel-v5-${SLURM_JOB_ID}}
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT
for ontology in 7581 4604 9663 10016 5566 8982 7127; do
  input=$corpus/ore_ont_${ontology}.owl
  for arm in v036 candidate; do
    if [[ $arm == v036 ]]; then bin=$v036; else bin=$candidate; fi
    timeout 300 /usr/bin/time -f '%e %M %x' -o "$work/${ontology}-${arm}.measure" \
      env KM_ROUTE=auto "$bin" classify "$input" > "$work/${ontology}-${arm}.json"
    read -r wall rss exit_code < "$work/${ontology}-${arm}.measure"
    echo "MEASURE ontology=$ontology arm=$arm wall=$wall rss_kib=$rss exit=$exit_code"
    [[ $exit_code == 0 ]]
    sha256sum "$work/${ontology}-${arm}.json"
  done
  cmp "$work/${ontology}-v036.json" "$work/${ontology}-candidate.json"
  read -r base_wall base_rss _ < "$work/${ontology}-v036.measure"
  read -r candidate_wall candidate_rss _ < "$work/${ontology}-candidate.measure"
  awk -v b="$base_wall" -v c="$candidate_wall" 'BEGIN { limit=b*1.25; if (limit < b+1) limit=b+1; exit !(c <= limit) }'
  awk -v b="$base_rss" -v c="$candidate_rss" 'BEGIN { exit !(c <= b*1.25) }'
  echo "MATCH_AND_RESOURCE_GUARD ontology=$ontology"
done
echo REGRESSION_PANEL_V5_COMPLETE
