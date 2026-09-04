#!/bin/bash
#SBATCH --job-name=km-v14-1194-zeroq
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-zeroq-20260831/slurm-%j.out

set -euo pipefail

binary=${KM_DIAG_BINARY:-/ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km}
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
root=${KM_DIAG_ROOT:-/ibex/scratch/hohndor/km/v14-1194-zeroq-20260831}
central_cap=${KM_DIAG_CENTRAL_CAP:-230}
outer_cap=$((central_cap + 10))
mkdir -p "$root"

binary_sha=${KM_DIAG_BINARY_SHA:-cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d}
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$binary_sha" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]

set +e
/usr/bin/time -v -o "$root/time.txt.tmp" \
  timeout --signal=TERM --kill-after=10 "$outer_cap" \
  env KM_ROUTE=manual \
      KM_COMP_IND_BITS=15 \
      KM_THREADS=1 \
      KM_PAR_MEM_GB=18 \
      KM_CENTRAL_TIME_CAP="$central_cap" \
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
      KM_PROF=1 \
      KM_PROF_TIME=1 \
      KM_MSGPROF=1 \
      KM_MEMSTATS=1 \
      "$binary" classify "$ontology" \
      > "$root/result.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e

mv "$root/time.txt.tmp" "$root/time.txt"
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
if [[ -s "$root/result.json.tmp" ]]; then
  /usr/bin/python3 -m json.tool "$root/result.json.tmp" > "$root/result.pretty.json"
  mv "$root/result.json.tmp" "$root/result.json"
else
  rm -f "$root/result.json.tmp"
fi
{
  echo "rc=$rc"
  echo "binary_sha256=$binary_sha"
  echo "ontology_sha256=$ontology_sha"
  echo "result_present=$([[ -s "$root/result.json" ]] && echo true || echo false)"
} > "$root/receipt.txt"
cat "$root/receipt.txt"
grep -E 'KM_TIMING|KM_STATS|KM_PROF|KM_MSGPROF|Maximum resident|Elapsed' \
  "$root/stderr.txt" "$root/time.txt" | tail -200 || true
