#!/bin/bash
#SBATCH --job-name=km_keep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:40:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/prof/keep/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
export MOOSE_HOME=$KM/moose
export PYTHONPATH=$KM/harness
export KM_PY_DIR=$KM/harness
export KM_PYBIN=python3
export KM_PYTHONPATH_OVR=$KM/harness
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_RUST_FRONTEND=1
export KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_RUST_EL=1
export KM_ELC_BIN=$KM/engine/target/release/elc
export KM_PAR_MEM_GB=18
export KM_ABSORB=1
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
export KM_THREADS=8
# all arms keep the auto-router on (no KM_SEQ_ORDER flag); add sound perf levers
ARMS=("auto:::" "auto_eu:::KM_EARLY_UNSAT=1" "auto_uf:::KM_TODO_UNITS_FIRST=1" "auto_both:::KM_EARLY_UNSAT=1 KM_TODO_UNITS_FIRST=1")
mapfile -t ONTS < $KM/prof/reg/onts.txt
NO=${#ONTS[@]}
ID=${SLURM_ARRAY_TASK_ID:-0}
ai=$(( ID / NO )); oi=$(( ID % NO ))
ENTRY=${ARMS[$ai]}; ARM=${ENTRY%%:::*}; ARMENV=${ENTRY#*:::}
ONT=${ONTS[$oi]}
for kv in $ARMENV; do export "$kv"; done
OUT=$KM/keep_out/$ARM; mkdir -p "$OUT"
RESDIR=$KM/keep_res; mkdir -p "$RESDIR"
RES=$RESDIR/${ARM}__${ONT}.res
t0=$SECONDS
JSON=$(python3 $KM/harness/ore_runone.py --reasoner km --ont $KM/corpus/ore_ont_${ONT}.owl \
    --outdir "$OUT" --timeout 240 --memcap-mb 20000 2>/dev/null)
wall=$(( SECONDS - t0 ))
status=$(printf '%s' "$JSON" | python3 -c "import json,sys
try: print(json.loads(sys.stdin.read()).get('status','?'))
except: print('parsefail')" 2>/dev/null)
KMSIG=$OUT/km__ore_ont_${ONT}.owl.sig.gz
GSIG=$KM/gold/konclude__ore_ont_${ONT}.owl.sig.gz
if [ -f "$KMSIG" ] && [ -f "$GSIG" ]; then
  if cmp -s <(zcat "$KMSIG" 2>/dev/null) <(zcat "$GSIG" 2>/dev/null); then GOLD=MATCH; else GOLD=DIFF; fi
else GOLD=NOSIG; fi
echo "ARM=$ARM ONT=$ONT STATUS=$status GOLD=$GOLD WALL=${wall}s" | tee "$RES"
