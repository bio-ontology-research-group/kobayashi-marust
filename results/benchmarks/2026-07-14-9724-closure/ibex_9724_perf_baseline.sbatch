#!/bin/bash
#SBATCH --job-name=km-9724-perf
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/perf-baseline-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$km_root/9663_closure_20260714/km-9663-final-bullseye
ontology=$km_root/corpus/ore_ont_9724.owl
run=$root/perf-baseline
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"

/usr/bin/perf record \
  --output="$run/perf.data" \
  --event=cycles:u \
  --freq=99 \
  --call-graph=dwarf,16384 \
  --inherit \
  -- \
  /usr/bin/timeout -k 5 90 \
  /usr/bin/env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=1 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=45 \
    KM_HT_MEM_GB=18 \
    KM_PAR_MEM_GB=18 \
    KM_THREADS=16 \
    "$binary" classify "$ontology" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"

/usr/bin/perf report \
  --input="$run/perf.data" \
  --stdio \
  --no-children \
  --percent-limit=0.25 \
  > "$run/perf-flat.txt"
/usr/bin/perf report \
  --input="$run/perf.data" \
  --stdio \
  --children \
  --percent-limit=0.5 \
  > "$run/perf-children.txt"

sed -n '1,160p' "$run/perf-flat.txt"
echo "END date=$(date -Is)"
