#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --export=NONE
#SBATCH --time=03:00:00
#SBATCH --job-name=km-v144-conformance
#SBATCH --array=0-59%20
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003/full-v144-final-admission-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003
reference=/ibex/scratch/hohndor/km/v143-harness-20260918
cd "$root"
sha256sum -c final-admission-binary.sha256
out="$root/full-v144-final-admission-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$out/tmp"
export TMPDIR="$out/tmp"
export HARNESS_OUT_DIR="$out/output"
unset KM_BRIDGE_PROGRESS KM_BRIDGE_PHASE_TIMING KM_RSUCC
unset KM_DATA_ABOX_PROJECT KM_GROUND_RULE_SOURCE KM_BRIDGE_NO_PRECOMPUTATION_REPLAY KM_BRIDGE_FRESH_ENV
unset KM_BRIDGE_NO_RETAINED_BASE KM_BRIDGE_NO_REPRESENTATIVE_CACHE
unset KM_UNARY_DATA_RULE_NORMALIZE KM_NO_UNARY_DATA_RULE_NORMALIZE KM_CONSTANT_DATA_RULE_NORMALIZE
unset KM_FINITE_DATA_RULE_NORMALIZE KM_NO_FINITE_DATA_RULE_NORMALIZE KM_FINITE_RULE_TAXONOMY KM_NO_FINITE_RULE_TAXONOMY
unset KM_RULE_JOIN_ORDER KM_RULE_ASSERTION_CLOSURE KM_TRANSITIVE_RULE_REDUCE
unset KM_SYMBOLIC_SOURCE_BRIDGE KM_NO_SYMBOLIC_SOURCE_BRIDGE KM_TRIGGER_ABSORB
export KM140_BIN="$root/km-final-admission"
lscpu > "$out/lscpu.txt"
chunk=$(printf '%03d' "$SLURM_ARRAY_TASK_ID")
cp "$reference/chunks/$chunk.txt" "$out/only.txt"
sha256sum "$out/only.txt" > "$out/manifest.sha256"
"$reference/target/release/owl-reasoner-harness" run \
 --corpus "$reference/corpus/pool_sample/files" --only "$out/only.txt" \
 --reasoner "$root/run-km-conformance-validation.sh" --args '{}' \
 --cap-secs 240 --threads 1 --mem-mb 20480 --out "$out/results.jsonl" \
 > "$out/driver.stdout" 2> "$out/driver.stderr"
touch "$out/COMPLETE"
