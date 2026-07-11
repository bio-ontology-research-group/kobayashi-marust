#!/bin/bash
#SBATCH --job-name=km-7914-cache-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/7914-cache-diag-%j.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$OUT/km-or-debug"
prefix="$OUT/7914-subject13031-cache-${SLURM_JOB_ID}"

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time"
/usr/bin/time -v -o "$prefix.time" \
  timeout 150 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_SAT_RESIDUE=1 KM_SAT_ABSORB_DEBUG=1 KM_SAT_COMMON_DEBUG_TAG=13041 \
    KM_SAT_COPY_DEBUG_TAG=${KM_SAT_COPY_DEBUG_TAG:-13041} \
    KM_SAT_INIT_DEBUG_TAG=${KM_SAT_INIT_DEBUG_TAG:-13041} \
    KM_SAT_FINAL_DEBUG_TAG=${KM_SAT_FINAL_DEBUG_TAG:-} \
    KM_SAT_SPECIAL_REF_OVERRIDE=${KM_SAT_SPECIAL_REF_OVERRIDE:-} \
    KM_SAT_ADD_TRACE=${KM_SAT_ADD_TRACE:-} \
    KM_SAT_ADD_TRACE_TAG=${KM_SAT_ADD_TRACE_TAG:-} \
    KM_BRIDGE_NAME_TAGS=37,61,112,138,1910,1912,5224,5227,5763,6271,6281 \
    KM_SAT_COMMON_DEBUG_OPERANDS=5224,5229,5237 KM_BRIDGE_CACHE_DEBUG=1 \
    KM_BRIDGE_ONLY_SUBJECT=13031 KM_BRIDGE_PROBE_BUDGET_S=10 KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 KM_HT_MEM_GB=88 KM_PAR_MEM_GB=88 \
    "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" \
    >"$prefix.json" 2>"$prefix.stderr"
rc=$?
echo "rc=$rc sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
tail -20 "$prefix.stderr"
