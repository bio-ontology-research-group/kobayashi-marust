#!/bin/bash
# Round 2: combination ablation. New base = absorbpf (KM_ABSORB_PORTFOLIO),
# the dominant single lever from round 1 (+4, 0 regress). Each arm =
# absorbpf + one combination delta. Targets: (a) can a combo crack any of the
# 18 unsolved (disjunction family via HT-absorption-forced + tab-cache)?
# (b) per-ont speed/mem-optimal among safe combos.
# Submit: sbatch --array=0-359 feat_ablate_r2.sbatch    (NARM=12 * NCHUNK=30)
#SBATCH --job-name=km_abl2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/abl_log2/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
cd $KM
export KM_BIN=$KM/engine/target/release/km
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_ELC_BIN=$KM/engine/target/release/elc
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
BASE_MEM_GB=18
BASE_THREADS=16
A="KM_ABSORB_PORTFOLIO=1 KM_ABSORB=1"   # the round-1 winner, common to all arms

ARMS=(
"a_base:::$A"
"a_nohtrace:::$A KM_NO_HT_RACE=1"
"a_elcforce:::$A KM_ELC_FORCE=1"
"a_tabrace:::$A KM_TAB_RACE=1 KM_TAB_CACHE=1"
"a_httrig:::$A KM_HT_TRIGABS=1 KM_HT_CONTRA=1 KM_HT_HARVEST=1"
"a_htrace_stack:::$A KM_HT_MODE=race KM_HT_TRIGABS=1 KM_HT_CONTRA=1 KM_HT_HARVEST=1"
"a_split:::$A KM_SPLIT=1"
"a_nocentral:::$A KM_NO_CENTRAL=1 KM_THREADS=1"
"a_corecap8:::$A KM_CORE_CAP=8"
"a_elc_tab:::$A KM_ELC_FORCE=1 KM_TAB_RACE=1 KM_TAB_CACHE=1"
"a_seqorder:::$A KM_SEQ_ORDER=1"
"a_kitchsink:::$A KM_ELC_FORCE=1 KM_TAB_RACE=1 KM_TAB_CACHE=1 KM_HT_TRIGABS=1 KM_HT_CONTRA=1 KM_HT_HARVEST=1"
)
NARM=${#ARMS[@]}
NCHUNK=30

ID=${SLURM_ARRAY_TASK_ID:-0}
ai=$(( ID / NCHUNK ))
ci=$(( ID % NCHUNK ))
[ $ai -ge $NARM ] && { echo "arm idx $ai out of range"; exit 0; }
ENTRY=${ARMS[$ai]}; ARM=${ENTRY%%:::*}; ARMENV=${ENTRY#*:::}

export KM_PAR_MEM_GB=$BASE_MEM_GB
export KM_THREADS=$BASE_THREADS
for kv in $ARMENV; do export "$kv"; done

OUT=$KM/abl_out2/$ARM; mkdir -p "$OUT"
RESDIR=$KM/abl_res2; mkdir -p "$RESDIR" "$KM/abl_log2"
RES=$RESDIR/${ARM}__c${ci}.jsonl
: > "$RES"

mapfile -t ALL < $KM/scored_onts.txt
li=0
for o in "${ALL[@]}"; do
  if [ $(( li % NCHUNK )) -eq $ci ]; then
    owl=$KM/corpus/ore_ont_${o}.owl
    gold=$KM/gold/konclude__ore_ont_${o}.owl.sig.gz
    if [ -f "$owl" ]; then
      JSON=$(python3 $KM/harness/ore_runone.py --reasoner km --ont "$owl" \
             --outdir "$OUT" --timeout 240 --memcap-mb 20000 2>>"$OUT/err.log")
      KMSIG=$OUT/km__ore_ont_${o}.owl.sig.gz
      if [ -f "$KMSIG" ] && [ -f "$gold" ]; then
        CMP=$(python3 $KM/sig_cmp.py "$KMSIG" "$gold" 2>/dev/null)
      else
        CMP="{}"
      fi
      python3 - "$JSON" "$CMP" "$ARM" >> "$RES" <<'PY'
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
    fi
  fi
  li=$(( li + 1 ))
done
echo "DONE arm=$ARM chunk=$ci -> $(wc -l < "$RES") onts"
