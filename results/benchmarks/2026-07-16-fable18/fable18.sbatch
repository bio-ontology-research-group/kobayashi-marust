#!/bin/bash
#SBATCH --job-name=km-fable18
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:50:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-71%36
#SBATCH --output=/ibex/scratch/hohndor/km/fable18_20260716/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km
audit=$root/fable18_20260716
runner=$root/routing_20260715/bench_one_matrix_frozen.py
gold_dir=$root/gold
corpus=$root/corpus
result_dir=$audit/results
failure_dir=$audit/failures

implementations=(cardinality rules kpset ordered)
ontologies=(
  ore_ont_541.owl
  ore_ont_1603.owl
  ore_ont_2669.owl
  ore_ont_3215.owl
  ore_ont_6934.owl
  ore_ont_7499.owl
  ore_ont_7581.owl
  ore_ont_7914.owl
  ore_ont_9540.owl
  ore_ont_9663.owl
  ore_ont_9724.owl
  ore_ont_10621.owl
  ore_ont_10702.owl
  ore_ont_12653.owl
  ore_ont_14817.owl
  ore_ont_15516.owl
  ore_ont_15672.owl
  ore_ont_15803.owl
)

task=${SLURM_ARRAY_TASK_ID:-0}
impl_index=$((task / 18))
ont_index=$((task % 18))
implementation=${implementations[$impl_index]}
ontology=${ontologies[$ont_index]}
binary=$audit/bin/km-$implementation
binary_sha=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
ontology_path=$corpus/$ontology
gold=$gold_dir/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-fable18-${SLURM_JOB_ID}_${task}
result=$result_dir/${implementation}__${ontology}.jsonl

/usr/bin/mkdir -p "$work" "$result_dir" "$failure_dir"

env_args=(--env KM_ROUTE=auto)
if [[ "$implementation" == ordered ]]; then
  env_args+=(--env KM_ROOT_ORDERED=1)
fi

/usr/bin/python3 "$runner" \
  --kind km \
  --arm "$implementation" \
  --ontology "$ontology_path" \
  --binary "$binary" \
  --binary-sha "$binary_sha" \
  --gold "$gold" \
  --gold-kind konclude \
  --workdir "$work" \
  --failures-dir "$failure_dir" \
  --order-index "$impl_index" \
  --timeout 240 \
  --memcap-mb 20480 \
  "${env_args[@]}" \
  > "$result"

/usr/bin/rm -rf "$work"
