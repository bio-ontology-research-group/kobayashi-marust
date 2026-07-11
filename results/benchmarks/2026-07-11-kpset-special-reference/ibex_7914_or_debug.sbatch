#!/bin/bash
#SBATCH --job-name=km-7914-or-debug
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/7914-or-debug-%j.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$OUT/km-or-debug"
PREFIX="$OUT/7914-or-debug"

rm -f "$PREFIX.json" "$PREFIX.stderr"
timeout 150 env \
  KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
  KM_SAT_OR_DEBUG_TAG=1440 KM_SAT_STATUS_DEBUG_TAG=1440 KM_SAT_LINK_DEBUG_TAG=1440 KM_BRIDGE_ONLY_SUBJECT=1430 \
  KM_BRIDGE_PROBE_BUDGET_S=1 KM_BRIDGE_RETRY_ROUNDS=0 \
  KM_HT_SATURATION_BUDGET_S=120 KM_HT_MEM_GB=88 KM_PAR_MEM_GB=88 \
  "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" \
  >"$PREFIX.json" 2>"$PREFIX.stderr"
rc=$?
grep '^SAT-OR-CHECK' "$PREFIX.stderr" || true
grep '^SAT-STATUS' "$PREFIX.stderr" || true
grep '^SAT-LINK' "$PREFIX.stderr" || true
echo "END rc=$rc sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
