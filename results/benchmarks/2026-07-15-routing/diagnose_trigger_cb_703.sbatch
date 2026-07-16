#!/bin/bash
# Determine whether ontology 703's seven missing pairs come from the isolated
# bridge, the trigger-compiled CB clause set, or only their race.
#SBATCH --job-name=km-trigger-cb-703
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/trigger-cb-703-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
ontology=ore_ont_703.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
work=${SLURM_TMPDIR:-/tmp}/km-trigger-cb-703-$SLURM_JOB_ID
out=$root/diagnose-trigger-cb-703.jsonl
fail=$root/diagnose-trigger-cb-703-failures
rm -rf "$work" "$fail"
mkdir -p "$work" "$fail"
: > "$out"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)

run() {
  local arm=$1
  shift
  local argv=(/usr/bin/python3 "$runner" --kind km --arm "$arm"
    --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha"
    --gold "$km_root/gold/konclude__$ontology.sig.gz"
    --workdir "$work" --failures-dir "$fail" --timeout 240 --memcap-mb 20480
    --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18
    --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_NO_ELC=1
    --env KM_NO_ABSORB_PORTFOLIO=1 --env KM_ABSORB=0
    --env KM_NO_HT_RACE=1)
  for setting in "$@"; do argv+=(--env "$setting"); done
  "${argv[@]}" >> "$out"
}

run plain
run trigger KM_TRIGGER_ABSORB=1
run trigger_single KM_TRIGGER_ABSORB=1 KM_THREADS=1
run trigger_seq_off KM_TRIGGER_ABSORB=1 KM_NO_SEQ_ORDER=1
run trigger_seq_on KM_TRIGGER_ABSORB=1 KM_SEQ_ORDER=1

cat "$out"
/usr/bin/rm -rf "$work" "$local_ontology"
