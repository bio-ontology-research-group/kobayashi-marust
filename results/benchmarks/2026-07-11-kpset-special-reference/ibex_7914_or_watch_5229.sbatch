#!/bin/bash
#SBATCH --job-name=km-7914-or-watch
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/7914-or-watch-%j.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$OUT/km-or-debug"
prefix="$OUT/7914-or-watch-5229-${SLURM_JOB_ID}"

rm -f "$prefix.json" "$prefix.stderr"
timeout 240 env \
  KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
  KM_BRIDGE_WATCH_TAG=5229 \
  KM_BRIDGE_ONLY_SUBJECT=13031 KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 \
  KM_HT_SATURATION_BUDGET_S=180 KM_HT_MEM_GB=88 KM_PAR_MEM_GB=88 \
  "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" \
  >"$prefix.json" 2>"$prefix.stderr"
rc=$?
echo "rc=$rc sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
echo "=== WATCH-OR-OPERAND lines ==="
grep '^WATCH-OR-OPERAND' "$prefix.stderr" | head -40 || true
echo "=== SAT-ROOT-READY / progress tail ==="
grep -E 'SAT-ROOT-READY|SAT-OR-CHECK' "$prefix.stderr" | head -20 || true
tail -15 "$prefix.stderr"
