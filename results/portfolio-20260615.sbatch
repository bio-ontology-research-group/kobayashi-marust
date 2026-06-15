#!/bin/bash
#SBATCH --job-name=km_pf
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/prof/pf/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
# common env (validated)
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

ARMS=(
"base:::"
"corecap4:::KM_CORE_CAP=4"
"corecap8:::KM_CORE_CAP=8"
"seedsubset:::KM_SEED_FROM_SUBSET=1"
"unitsfirst:::KM_TODO_UNITS_FIRST=1"
"earlyunsat:::KM_EARLY_UNSAT=1"
"combo:::KM_CORE_CAP=4 KM_SEED_FROM_SUBSET=1 KM_TODO_UNITS_FIRST=1 KM_EARLY_UNSAT=1"
"nocentral:::KM_NO_CENTRAL=1 KM_THREADS=1"
"highcap:::KM_MSG_CAP=200000000"
"split:::KM_SPLIT=1"
"seqorder:::KM_SEQ_ORDER=1"
"notrigskip:::KM_NO_TRIGSKIP=1"
"threads16:::KM_THREADS=16"
"tabrace:::KM_TAB_RACE=1 KM_TAB_CACHE=1"
)
ONTS=(10621 10702 10860 10908 11016 11291 11460 1194 12141 12653 14817 15491 15516 15672 15803 1603 2669 3215 4604 4669 5107 5303 541 6246 6682 6934 7246 7499 7581 7914 8737 9024 9540 9635 9663 9724)
NO=${#ONTS[@]}
ID=${SLURM_ARRAY_TASK_ID:-0}
ai=$(( ID / NO )); oi=$(( ID % NO ))
ENTRY=${ARMS[$ai]}; ARM=${ENTRY%%:::*}; ARMENV=${ENTRY#*:::}
ONT=${ONTS[$oi]}

# default threads (arm env may override below)
export KM_THREADS=8
for kv in $ARMENV; do export "$kv"; done

OUT=$KM/pf_out/$ARM; mkdir -p "$OUT"
RESDIR=$KM/pf_res; mkdir -p "$RESDIR"
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
else
  GOLD=NOSIG
fi
echo "ARM=$ARM ONT=$ONT STATUS=$status GOLD=$GOLD WALL=${wall}s ENV=[$ARMENV]" | tee "$RES"
