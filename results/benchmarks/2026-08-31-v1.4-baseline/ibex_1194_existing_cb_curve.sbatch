#!/bin/bash
#SBATCH --job-name=km-v14-1194-cb
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --time=00:12:00
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-existing-cb-20260831/slurm-%A_%a.out

set -euo pipefail

threads=(1 2 4)
n=${KM_DIAG_THREADS:-${threads[$SLURM_ARRAY_TASK_ID]}}
query_batch=${KM_DIAG_QUERY_BATCH:-0}
binary=/ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
root=/ibex/scratch/hohndor/km/v14-1194-existing-cb-20260831
out=$root/threads-$n-batch-$query_batch
mkdir -p "$out"

[[ $(sha256sum "$binary" | cut -d' ' -f1) == cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == 72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2 ]]

set +e
/usr/bin/time -v -o "$out/time.txt" \
  timeout --signal=TERM --kill-after=10 650 \
  env KM_ROUTE=manual \
      KM_COMP_IND_BITS=15 \
      KM_THREADS="$n" \
      KM_QUERY_BATCH="$query_batch" \
      KM_PAR_MEM_GB=22 \
      KM_CENTRAL_TIME_CAP=600 \
      KM_MECHANISM=cb \
      KM_NO_ELC=1 \
      KM_NO_HT_RACE=1 \
      KM_NO_HT_RULES=1 \
      KM_NO_ABSORB_PORTFOLIO=1 \
      KM_NO_RETRY=1 \
      KM_ABSORB=0 \
      KM_NOMINALS=1 \
      KM_TIMING=1 \
      KM_STATS=1 \
      "$binary" classify "$ontology" \
      > "$out/result.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
if [[ -s "$out/result.json.tmp" ]]; then
  /usr/bin/python3 -m json.tool "$out/result.json.tmp" > "$out/result.pretty.json"
  mv "$out/result.json.tmp" "$out/result.json"
else
  rm -f "$out/result.json.tmp"
fi
{
  echo "rc=$rc"
  echo "threads=$n"
  echo "query_batch=$query_batch"
  echo "binary_sha256=$(sha256sum "$binary" | cut -d' ' -f1)"
  echo "ontology_sha256=$(sha256sum "$ontology" | cut -d' ' -f1)"
  echo "result_present=$([[ -s "$out/result.json" ]] && echo true || echo false)"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
grep -E 'KM_TIMING|KM_STATS|Maximum resident|Elapsed' "$out/stderr.txt" "$out/time.txt" | tail -80 || true
