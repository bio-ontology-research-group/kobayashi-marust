#!/bin/bash
# Targeted probe: can ANY aggressive flag combination + extra resources recover
# the 18 onts unsolved by all 53 prior configs? Cheap (18 onts only), 600s/40GB,
# hypothesis-driven combos per failure family. Separates resource-bound from
# algorithm-bound. Per-(arm,ont) array, one ont per task.
# Submit: sbatch --array=0-179 probe18.sbatch    (NARM=10 * NONT=18)
#SBATCH --job-name=km_p18
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=44G
#SBATCH --output=/ibex/scratch/hohndor/km/p18_log/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
cd $KM
export KM_BIN=$KM/engine/target/release/km
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_ELC_BIN=$KM/engine/target/release/elc
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
A="KM_ABSORB_PORTFOLIO=1 KM_ABSORB=1"

ARMS=(
"p_ctrl600:::$A"
"p_dirC:::$A KM_SPLIT=1 KM_TAB_RACE=1 KM_TAB_CACHE=1"
"p_dirC_conv:::$A KM_SPLIT=1 KM_TAB_RACE=1 KM_TAB_CACHE=1 KM_TAB_CONV=1"
"p_ord_split:::$A KM_SEQ_ORDER=1 KM_SPLIT=1"
"p_orderedall:::$A KM_ORDERED_ALL=1 KM_SPLIT=1"
"p_leanmax:::$A KM_NO_HT_RACE=1 KM_NO_ELC_PORTFOLIO=1 KM_NO_CENTRAL=1 KM_THREADS=1"
"p_lowmem:::$A KM_NO_ELC_PORTFOLIO=1 KM_NO_CENTRAL=1 KM_THREADS=1"
"p_elcforce:::$A KM_ELC_FORCE=1 KM_ELC_FORCE_BUDGET_S=400"
"p_htforce:::$A KM_HT_FORCE=1 KM_HT_MODE=race"
"p_kitchen:::$A KM_SPLIT=1 KM_TAB_RACE=1 KM_TAB_CACHE=1 KM_SEQ_ORDER=1 KM_HT_LEARN=1 KM_HT_TRIGABS=1 KM_HT_HARVEST=1"
)
ONTS=(541 1603 2669 3215 6934 7499 7581 7914 9540 9663 9724 10621 10702 12653 14817 15516 15672 15803)
NARM=${#ARMS[@]}
NONT=${#ONTS[@]}

ID=${SLURM_ARRAY_TASK_ID:-0}
ai=$(( ID / NONT )); oi=$(( ID % NONT ))
[ $ai -ge $NARM ] && exit 0
ENTRY=${ARMS[$ai]}; ARM=${ENTRY%%:::*}; ARMENV=${ENTRY#*:::}
ONT=${ONTS[$oi]}

export KM_PAR_MEM_GB=38
export KM_THREADS=16
for kv in $ARMENV; do export "$kv"; done

OUT=$KM/p18_out/$ARM; mkdir -p "$OUT"
RESDIR=$KM/p18_res; mkdir -p "$RESDIR" "$KM/p18_log"
RES=$RESDIR/${ARM}__${ONT}.jsonl
owl=$KM/corpus/ore_ont_${ONT}.owl
gold=$KM/gold/konclude__ore_ont_${ONT}.owl.sig.gz
JSON=$(python3 $KM/harness/ore_runone.py --reasoner km --ont "$owl" \
       --outdir "$OUT" --timeout 600 --memcap-mb 40000 2>>"$OUT/err.log")
KMSIG=$OUT/km__ore_ont_${ONT}.owl.sig.gz
if [ -f "$KMSIG" ] && [ -f "$gold" ]; then CMP=$(python3 $KM/sig_cmp.py "$KMSIG" "$gold" 2>/dev/null); else CMP="{}"; fi
python3 - "$JSON" "$CMP" "$ARM" > "$RES" <<'PY'
import json,sys
try: r=json.loads(sys.argv[1])
except Exception: r={"status":"parsefail"}
try: c=json.loads(sys.argv[2] or "{}")
except Exception: c={}
r["arm"]=sys.argv[3]
for k,v in c.items(): r["cmp_"+k]=v
print(json.dumps(r))
PY
rm -f "$KMSIG"
echo "DONE $ARM $ONT"
