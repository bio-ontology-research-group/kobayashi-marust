#!/bin/bash
# Recheck the 14 matrix-union failures through the current additive production
# route. One ontology per allocation; the ontology stays on shared scratch so
# worker subprocesses do not depend on Slurm step-local /tmp namespaces.
#SBATCH --job-name=km-remaining14
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-13%14
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/remaining14-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix-3b1d2a87.py
km=$root/km-current-remaining14
gold_dir=$km_root/gold
result_dir=$root/remaining14-current
failure_dir=$root/remaining14-current-failures
work=${SLURM_TMPDIR:-/tmp}/km-remaining14-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

onts=(
  ore_ont_10621.owl
  ore_ont_10702.owl
  ore_ont_10860.owl
  ore_ont_10908.owl
  ore_ont_1194.owl
  ore_ont_15516.owl
  ore_ont_15672.owl
  ore_ont_15703.owl
  ore_ont_2669.owl
  ore_ont_3215.owl
  ore_ont_3524.owl
  ore_ont_6934.owl
  ore_ont_7499.owl
  ore_ont_9540.owl
)

ontology=${onts[${SLURM_ARRAY_TASK_ID:-0}]}
ontology_path=$km_root/corpus/$ontology
gold=$gold_dir/konclude__$ontology.sig.gz
result=$result_dir/$ontology.jsonl
/usr/bin/mkdir -p "$result_dir" "$failure_dir" "$work"

case "$ontology" in
  ore_ont_10860.owl|ore_ont_1194.owl|ore_ont_15703.owl|ore_ont_3524.owl)
    gold_args=(--gold-kind none)
    ;;
  *)
    gold_args=(--gold "$gold" --gold-kind konclude)
    ;;
esac

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
/usr/bin/python3 "$runner" \
  --kind km --arm production_all --ontology "$ontology_path" \
  --binary "$km" --binary-sha "$km_sha" \
  "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir" \
  --order-index 0 --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=production_all > "$result"

/usr/bin/rm -rf "$work"
/usr/bin/printf 'DONE ontology=%s\n' "$ontology"
