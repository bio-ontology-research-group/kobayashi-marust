#!/bin/bash
# Comprehensive per-feature ablation sweep over the ORE-2015 scored corpus.
# Each array task = one (arm, chunk). arm = baseline + one KM_* delta.
# Baseline = `km classify` with explicit worker bins, all features default.
# Round-robin ont->chunk so timeouts/giants spread across chunks.
#
# Submit: sbatch --array=0-959 feat_ablate.sbatch     (NARM=32 * NCHUNK=30)
#SBATCH --job-name=km_abl
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/abl_log/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
cd $KM

# ---- baseline env (the deployed `km classify` production path) -------------
export KM_BIN=$KM/engine/target/release/km
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_ELC_BIN=$KM/engine/target/release/elc
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
BASE_MEM_GB=18
BASE_THREADS=16

# ---- arms: name:::extra-env (space separated KEY=VAL) ----------------------
ARMS=(
"base:::"
"absorbpf:::KM_ABSORB_PORTFOLIO=1 KM_ABSORB=1"
"seqorder:::KM_SEQ_ORDER=1"
"noseqorder:::KM_NO_SEQ_ORDER=1"
"split:::KM_SPLIT=1"
"orderedall:::KM_ORDERED_ALL=1"
"ctxsplit:::KM_CTXSPLIT=1"
"tabrace:::KM_TAB_RACE=1 KM_TAB_CACHE=1"
"elcforce:::KM_ELC_FORCE=1"
"nominals:::KM_NOMINALS=1"
"corecap4:::KM_CORE_CAP=4"
"seedsubset:::KM_SEED_FROM_SUBSET=1"
"unitsfirst:::KM_TODO_UNITS_FIRST=1"
"htracemode:::KM_HT_MODE=race"
"staticsched:::KM_STATIC_SCHED=1"
"nocentral:::KM_NO_CENTRAL=1 KM_THREADS=1"
"nochaindom:::KM_NO_CHAIN_DOMAIN=1"
"nodatatypes:::KM_NO_DATATYPES=1"
"noshare:::KM_NO_SHARE=1"
"noprune:::KM_NO_PRUNE=1"
"noearlyunsat:::KM_NO_EARLY_UNSAT=1"
"notrigskip:::KM_NO_TRIGSKIP=1"
"noelcpf:::KM_NO_ELC_PORTFOLIO=1"
"nohtrace:::KM_NO_HT_RACE=1"
"noretry:::KM_NO_RETRY=1"
"httrigabs:::KM_HT_TRIGABS=1 KM_HT_CONTRA=1"
"htharvest:::KM_HT_HARVEST=1"
"htblock3:::KM_HT_BLOCK=3"
"htqo:::KM_HT_QO=1"
"htlearn:::KM_HT_LEARN=1"
"htcaches:::KM_HT_SATCACHE=1 KM_HT_UNSATCACHE=1 KM_HT_CACHE=1"
"htblockskip:::KM_HT_BLOCKSKIP=1"
)
NARM=${#ARMS[@]}
NCHUNK=30

ID=${SLURM_ARRAY_TASK_ID:-0}
ai=$(( ID / NCHUNK ))
ci=$(( ID % NCHUNK ))
[ $ai -ge $NARM ] && { echo "arm idx $ai out of range"; exit 0; }
ENTRY=${ARMS[$ai]}; ARM=${ENTRY%%:::*}; ARMENV=${ENTRY#*:::}

# apply baseline knobs then the arm delta (arm may override threads, e.g. nocentral)
export KM_PAR_MEM_GB=$BASE_MEM_GB
export KM_THREADS=$BASE_THREADS
for kv in $ARMENV; do export "$kv"; done

OUT=$KM/abl_out/$ARM; mkdir -p "$OUT"
RESDIR=$KM/abl_res; mkdir -p "$RESDIR" "$KM/abl_log"
RES=$RESDIR/${ARM}__c${ci}.jsonl
: > "$RES"

# scored onts assigned to this chunk (round-robin by line index)
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
      rm -f "$KMSIG"   # correctness already extracted into the jsonl record
    fi
  fi
  li=$(( li + 1 ))
done
echo "DONE arm=$ARM chunk=$ci -> $(wc -l < "$RES") onts"
