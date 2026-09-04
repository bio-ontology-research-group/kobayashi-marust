#!/bin/bash
#SBATCH --job-name=km-v14-1194-paired
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-zeroq-paired-20260901/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-1194-zeroq-paired-20260901
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
mkdir -p "$root"

run_arm() {
  local name=$1 binary=$2 expected=$3
  local out=$root/$name
  mkdir -p "$out"
  [[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
  set +e
  /usr/bin/time -v -o "$out/time.txt.tmp" \
    timeout --signal=TERM --kill-after=10 55 \
    env KM_ROUTE=manual \
        KM_COMP_IND_BITS=15 \
        KM_THREADS=1 \
        KM_PAR_MEM_GB=18 \
        KM_CENTRAL_TIME_CAP=40 \
        KM_MECHANISM=cb \
        KM_NO_ELC=1 \
        KM_NO_HT_RACE=1 \
        KM_NO_HT_RULES=1 \
        KM_NO_ABSORB_PORTFOLIO=1 \
        KM_NO_RETRY=1 \
        KM_ABSORB=0 \
        KM_NOMINALS=1 \
        KM_QUERIES=__none__ \
        KM_TIMING=1 \
        KM_STATS=1 \
        KM_PROF_TIME=1 \
        KM_MEMSTATS=1 \
        "$binary" classify "$ontology" \
        > "$out/result.json.tmp" 2> "$out/stderr.txt.tmp"
  local rc=$?
  set -e
  mv "$out/time.txt.tmp" "$out/time.txt"
  mv "$out/stderr.txt.tmp" "$out/stderr.txt"
  rm -f "$out/result.json.tmp"
  {
    echo "rc=$rc"
    echo "binary_sha256=$expected"
    echo "ontology_sha256=$ontology_sha"
    echo "host=$(hostname)"
  } > "$out/receipt.txt"
}

run_arm baseline \
  /ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km \
  cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
run_arm adaptive \
  /ibex/scratch/hohndor/km/v14-pool-index-bitset-20260901/km-ibex \
  5a8952715ab38b91af7bdd876d3b8c65e7feeb7df08e1e8700e0592cab5eebe9

for out in "$root"/baseline "$root"/adaptive; do
  echo "=== $(basename "$out") ==="
  cat "$out/receipt.txt"
  grep -E 'KM_STATS|KM_MEMSTATS|Elapsed|Maximum resident|Exit status' \
    "$out/stderr.txt" "$out/time.txt" | tail -80 || true
done
