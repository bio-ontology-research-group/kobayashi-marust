#!/bin/bash
# Full-corpus measurement of the cb_absorb_portfolio16 named route, which
# recovered ore_ont_10908 in the remaining-route grid.
#SBATCH --job-name=km-absorbpf-full
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%48
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/absorbpf-full-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix-3b1d2a87.py
km=$root/km-current-remaining14
gold_dir=$km_root/gold
result_dir=$root/cb-absorb-portfolio16-full
failure_dir=$root/cb-absorb-portfolio16-full-failures
work=${SLURM_TMPDIR:-/tmp}/km-absorbpf-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

mapfile -t ontologies < "$root/onts.txt"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
ontology_path=$km_root/corpus/$ontology
gold=$gold_dir/konclude__$ontology.sig.gz
result=$result_dir/$ontology.jsonl
/usr/bin/mkdir -p "$result_dir" "$failure_dir" "$work"

case "$ontology" in
  ore_ont_10860.owl|ore_ont_1194.owl|ore_ont_15703.owl|ore_ont_3524.owl|ore_ont_4669.owl)
    gold_args=(--gold-kind none)
    ;;
  *)
    gold_args=(--gold "$gold" --gold-kind konclude)
    ;;
esac

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
/usr/bin/python3 "$runner" \
  --kind km --arm cb_absorb_portfolio16 --ontology "$ontology_path" \
  --binary "$km" --binary-sha "$km_sha" \
  "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir" \
  --order-index 0 --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=cb_absorb_portfolio16 > "$result"

/usr/bin/rm -rf "$work"
/usr/bin/printf 'DONE ontology=%s\n' "$ontology"
