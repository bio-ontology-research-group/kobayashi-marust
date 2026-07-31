#!/bin/bash
# Distinguish query-collapse impact from changes already present in v14.
#SBATCH --job-name=km-query-eq-15846-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/query-equivalence-20260731/ablation-15846/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/query-equivalence-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_15846.owl
index=${SLURM_ARRAY_TASK_ID:?}
if [[ "$index" == 0 ]]; then
  label=candidate_no_query_equiv
  binary=$root/km
  extra=(--env KM_NO_QUERY_EQUIV=1)
else
  label=v14_baseline
  binary=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731/km
  extra=()
fi
work=${SLURM_TMPDIR:-/tmp}/km-query-eq-15846-ab-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/ablation-15846"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_15846_$label" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$binary" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/ablation-15846" \
  --checkpoint "$root/ablation-15846/$label.checkpoint.json" \
  --env KM_ROUTE=auto \
  "${extra[@]}" \
  >"$root/ablation-15846/$label.json.tmp"
/usr/bin/mv "$root/ablation-15846/$label.json.tmp" \
  "$root/ablation-15846/$label.json"
