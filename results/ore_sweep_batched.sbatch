#!/bin/bash
# Batched ORE sweep: ~10 onts per array task (587 onts -> ~59 tasks; stays well
# under the IBEX 2000-job submit cap). Submit with:  sbatch --array=0-58%40 ...
# Per-task env arms via $ARM (default auto-router on). Writes per-ont .res files.
#SBATCH --job-name=km_sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=2:00:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/prof/sweep/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
export MOOSE_HOME=$KM/moose PYTHONPATH=$KM/harness KM_PY_DIR=$KM/harness
export KM_PYBIN=python3 KM_PYTHONPATH_OVR=$KM/harness
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_RUST_FRONTEND=1 KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_RUST_EL=1 KM_ELC_BIN=$KM/engine/target/release/elc
export KM_PAR_MEM_GB=18 KM_THREADS=8
export KM_ABSORB=1 KM_ABSORB_PORTFOLIO=1 KM_TAB_RACE=1
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
# extra per-run env (e.g. KM_NO_SEQ_ORDER=1) via the CHUNKENV submit var
for kv in ${CHUNKENV:-}; do export "$kv"; done
PER=${PER:-10}
mapfile -t ALL < $KM/prof/reg/onts.txt
ID=${SLURM_ARRAY_TASK_ID:-0}
start=$(( ID * PER ))
RESDIR=$KM/${RESTAG:-sweep}_res; OUT=$KM/${RESTAG:-sweep}_out; mkdir -p "$RESDIR" "$OUT"
for off in $(seq 0 $(( PER - 1 ))); do
  idx=$(( start + off )); [ $idx -ge ${#ALL[@]} ] && break
  ONT=${ALL[$idx]}
  JSON=$(python3 $KM/harness/ore_runone.py --reasoner km --ont $KM/corpus/ore_ont_${ONT}.owl \
      --outdir "$OUT" --timeout 240 --memcap-mb 20000 2>/dev/null)
  status=$(printf '%s' "$JSON" | python3 -c "import json,sys
try: print(json.loads(sys.stdin.read()).get('status','?'))
except: print('parsefail')" 2>/dev/null)
  KMSIG=$OUT/km__ore_ont_${ONT}.owl.sig.gz; GSIG=$KM/gold/konclude__ore_ont_${ONT}.owl.sig.gz
  if [ -f "$KMSIG" ] && [ -f "$GSIG" ]; then
    if cmp -s <(zcat "$KMSIG" 2>/dev/null) <(zcat "$GSIG" 2>/dev/null); then GOLD=MATCH; else GOLD=DIFF; fi
  else GOLD=NOSIG; fi
  echo "ONT=$ONT STATUS=$status GOLD=$GOLD" | tee "$RESDIR/${ONT}.res"
done
