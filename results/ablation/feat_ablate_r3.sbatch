#!/bin/bash
# Round 3: GREEDY COMBINATION of the individually-improving flags, with the focus
# on avg+median TIME and MEM (not just pass/fail). Anchor = absorbpf (the
# coverage max). Tests: (a) do coverage-safe speed flags stack to speed up the
# HT-heavy onts while holding 569? (b) the time/mem Pareto frontier: stack the
# racer-drop levers (nohtrace, noelcpf, nocentral) and measure the combined
# speed+mem win vs the coverage cost.
# Submit: sbatch --array=0-269 feat_ablate_r3.sbatch     (NARM=9 * NCHUNK=30)
#SBATCH --job-name=km_abl3
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/abl_log3/slurm-%A_%a.out
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
A="KM_ABSORB_PORTFOLIO=1 KM_ABSORB=1"

ARMS=(
"r3_absorb:::$A"
"r3_htspeed:::$A KM_HT_LEARN=1 KM_HT_SATCACHE=1 KM_HT_UNSATCACHE=1 KM_HT_CACHE=1 KM_HT_TRIGABS=1 KM_HT_HARVEST=1"
"r3_covsafe:::$A KM_HT_LEARN=1 KM_HT_TRIGABS=1 KM_HT_HARVEST=1 KM_ELC_FORCE=1 KM_TAB_RACE=1 KM_TAB_CACHE=1"
"r3_covneutral:::$A KM_NO_SHARE=1 KM_NO_EARLY_UNSAT=1"
"r3_nohtrace:::$A KM_NO_HT_RACE=1"
"r3_noelc:::$A KM_NO_ELC_PORTFOLIO=1"
"r3_lean:::$A KM_NO_HT_RACE=1 KM_NO_ELC_PORTFOLIO=1"
"r3_leanmax:::$A KM_NO_HT_RACE=1 KM_NO_ELC_PORTFOLIO=1 KM_NO_CENTRAL=1 KM_THREADS=1"
"r3_lowmem:::$A KM_NO_ELC_PORTFOLIO=1 KM_NO_CENTRAL=1 KM_THREADS=1"
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

OUT=$KM/abl_out3/$ARM; mkdir -p "$OUT"
RESDIR=$KM/abl_res3; mkdir -p "$RESDIR" "$KM/abl_log3"
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
