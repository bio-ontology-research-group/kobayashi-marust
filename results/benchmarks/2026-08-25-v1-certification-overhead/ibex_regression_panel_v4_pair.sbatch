#!/bin/bash
#SBATCH --job-name=km-v110-panel-v4
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v4-20260825/panel-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v4-20260825
corpus=/ibex/scratch/hohndor/km/corpus
v036=/ibex/scratch/hohndor/km/v036-large-clean-20260815/km
candidate=$root/km
[[ $(sha256sum "$v036" | cut -d' ' -f1) == bbef8d7efbc6a6b8aefa3c44e55f40fb90916f1974d6c8086eb77bb7ac1d074f ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == 4d5bc52a185ce52aa8dedd4bafceac45d7ed67fb1392cf2d64161bb94261c534 ]]
work=${SLURM_TMPDIR:-/tmp/km-v110-panel-v4-${SLURM_JOB_ID}}
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT
for ontology in 7581 4604 9663 10016 5566 8982 7127; do
  input=$corpus/ore_ont_${ontology}.owl
  for arm in v036 candidate; do
    if [[ $arm == v036 ]]; then bin=$v036; else bin=$candidate; fi
    echo "BEGIN ontology=$ontology arm=$arm"
    timeout 300 /usr/bin/time -f "MEASURE ontology=$ontology arm=$arm wall=%e rss_kib=%M exit=%x" \
      env KM_ROUTE=auto "$bin" classify "$input" > "$work/${ontology}-${arm}.json" 2> "$work/${ontology}-${arm}.stderr"
    grep '^MEASURE ' "$work/${ontology}-${arm}.stderr"
    sha256sum "$work/${ontology}-${arm}.json"
  done
  cmp "$work/${ontology}-v036.json" "$work/${ontology}-candidate.json"
  echo "MATCH ontology=$ontology"
done
echo REGRESSION_PANEL_V4_COMPLETE
