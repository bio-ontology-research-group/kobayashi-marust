#!/bin/bash
#SBATCH --job-name=km-v14-uberon-rules-stats
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904/slurm-%j.out
set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904
bin=/ibex/scratch/hohndor/km/v14-uberon-rules-profile-20260904/km-branch-profile-native
ont=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged/uberon.ofn
mkdir -p "$root"
test "$(sha256sum "$bin" | awk '{print $1}')" = 2eb8f5619737812b9651765db1648fa401218716ec144f62369aefd09e59a362
cpu_model=$(awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
set +e
/usr/bin/time -v -o "$root/time.txt" /usr/bin/timeout -k 10 60 \
  /usr/bin/env KM_ROUTE=manual KM_MECHANISM=cb KM_NOMINALS=1 KM_THREADS=2 \
  KM_TAB_BIN=/ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904/profile-tableau-wrapper.sh \
  KM_PAR_MEM_GB=7 KM_CENTRAL_TIME_CAP=50 KM_NO_RETRY=1 \
  KM_ABSORB=1 KM_TRIGGER_ABSORB=1 KM_TIMING=1 KM_TAB_STATS=1 \
  "$bin" classify "$ont" >"$root/output.json" 2>"$root/stderr.log"
rc=$?
set -e
{
  printf 'job_id\t%s\n' "$SLURM_JOB_ID"
  printf 'exit_code\t%s\n' "$rc"
  printf 'host\t%s\n' "$(hostname)"
  printf 'cpu_model\t%s\n' "$cpu_model"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$bin" | awk '{print $1}')"
  printf 'ontology_sha256\t%s\n' "$(sha256sum "$ont" | awk '{print $1}')"
  printf 'output_bytes\t%s\n' "$(wc -c < "$root/output.json")"
} >"$root/receipt.tsv"
echo DIAGNOSTIC_COMPLETE
