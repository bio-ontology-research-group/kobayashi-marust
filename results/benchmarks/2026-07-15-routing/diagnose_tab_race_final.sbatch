#!/bin/bash
# Isolate the historical cache-tableau closure of ore_ont_9635.  The outer EL
# and HT portfolios, in-process CB probe, absorption portfolio, and lazy delay
# are disabled so only plain CB versus the faithfully converted legacy tableau
# remains.  tab_capture.sh preserves the exact TInput and worker stderr.
#SBATCH --job-name=km-tab-route-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/tab-diag-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final2
ontology=ore_ont_9635.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
gold=$km_root/gold/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-tab-diag-$SLURM_JOB_ID
result=$root/diagnose-tab-race-final2.jsonl
failure_dir=$root/diagnose-tab-race-failures
mkdir -p "$work" "$failure_dir" "$root/slurm"
: > "$result"
: > "$root/tab-9635-final2.stderr"
rm -f "$root/tab-9635-final2.tin.json"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)

/usr/bin/python3 "$runner" --kind km --arm tab_race_isolated \
  --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha" \
  --gold "$gold" --workdir "$work" --failures-dir "$failure_dir" \
  --timeout 90 --memcap-mb 20480 \
  --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
  --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_NO_ELC=1 \
  --env KM_NO_HT_RACE=1 --env KM_NO_INPROC_ENGINE=1 \
  --env KM_NO_ABSORB_PORTFOLIO=1 --env KM_ABSORB=0 \
  --env KM_TAB_RACE=1 --env KM_TAB_FEAT=1 --env KM_TAB_RACE_DELAY=0 \
  --env KM_TAB_RACE_NICE=0 --env KM_TAB_BIN="$root/tab_capture.sh" \
  >> "$result"

/usr/bin/printf 'TIN_BYTES=%s STDERR_BYTES=%s\n' \
  "$(/usr/bin/stat -c %s "$root/tab-9635-final2.tin.json" 2>/dev/null || echo 0)" \
  "$(/usr/bin/stat -c %s "$root/tab-9635-final2.stderr" 2>/dev/null || echo 0)"
/usr/bin/rm -rf "$work" "$local_ontology"
