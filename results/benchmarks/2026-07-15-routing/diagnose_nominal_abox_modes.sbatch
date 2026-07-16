#!/bin/bash
# Diagnose exact nominal/ABox scaling without changing the immutable matrix.
# Each task runs the same calculus with central/per-function scheduling only.
#SBATCH --job-name=km-nominal-abox-modes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/nominal-abox-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=${DIAG_RUNNER:-$root/bench_one_matrix-3b1d2a87.py}
km=${DIAG_KM:-$root/km-source-symbol-c229366f}
result_dir=${DIAG_RESULT_DIR:-$root/nominal-abox-modes-c229366f}
failure_dir=${DIAG_FAILURE_DIR:-$root/failures-nominal-abox-modes-c229366f}
work=${SLURM_TMPDIR:-/tmp}/km-nominal-abox-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
/usr/bin/mkdir -p "$work" "$result_dir" "$failure_dir" "$root/slurm"

ontologies=(ore_ont_10697.owl ore_ont_15725.owl ore_ont_15846.owl)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
local_ontology=$work/$ontology
result=$result_dir/$ontology.jsonl
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
: > "$result"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)

common=(
  --env KM_ROUTE=manual
  --env KM_MECHANISM=cb
  --env KM_PAR_MEM_GB=18
  --env KM_HT_MEM_GB=18
  --env KM_KEEP_CHAIN_AXIOMS=1
  --env KM_NO_ELC=1
  --env KM_NO_HT_RACE=1
  --env KM_NO_HT_RULES=1
  --env KM_NO_ABSORB_PORTFOLIO=1
  --env KM_NO_RETRY=1
  --env KM_ABSORB=0
  --env KM_NOMINALS=1
)

position=0
for mode in central1 perfn1 perfn8 perfn16; do
  settings=()
  case "$mode" in
    central1) settings=(--env KM_THREADS=1) ;;
    perfn1) settings=(--env KM_THREADS=1 --env KM_NO_CENTRAL=1) ;;
    perfn8) settings=(--env KM_THREADS=8 --env KM_NO_CENTRAL=1) ;;
    perfn16) settings=(--env KM_THREADS=16 --env KM_NO_CENTRAL=1) ;;
  esac
  /usr/bin/python3 "$runner" \
    --kind km --arm "nominal_$mode" --ontology "$local_ontology" \
    --binary "$km" --binary-sha "$km_sha" \
    --gold "$km_root/gold/konclude__$ontology.sig.gz" --gold-kind konclude \
    --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$position" --timeout 240 --memcap-mb 20480 \
    "${common[@]}" "${settings[@]}" >> "$result"
  position=$((position + 1))
done

/usr/bin/rm -rf "$work"
