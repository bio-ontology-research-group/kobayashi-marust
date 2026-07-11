#!/bin/bash
#SBATCH --job-name=km-7914-sat-residue
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/7914-sat-residue-%j.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$OUT/km-or-debug"
PREFIX="$OUT/7914-sat-residue"

rm -f "$PREFIX.json" "$PREFIX.stderr"
echo "BEGIN host=$(hostname) date=$(date -Is) sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
timeout 180 env \
  KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 \
  KM_BRIDGE_PROGRESS=1 KM_BRIDGE_SAT_RESIDUE=1 KM_BRIDGE_ONLY_SUBJECT=13031 \
  KM_BRIDGE_PROBE_BUDGET_S=1 KM_BRIDGE_RETRY_ROUNDS=0 \
  KM_HT_SATURATION_BUDGET_S=150 KM_HT_MEM_GB=88 KM_PAR_MEM_GB=88 \
  "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" \
  > "$PREFIX.json" 2> "$PREFIX.stderr"
rc=$?
grep -c '^BRIDGE-SATURATION-RESIDUE ' "$PREFIX.stderr" || true
echo "END rc=$rc date=$(date -Is)"
