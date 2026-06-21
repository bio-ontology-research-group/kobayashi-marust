#!/bin/bash
# Per-ont OPTIMAL-config lattice. Knowledge-based factorial over the orthogonal
# time/mem levers (threads x elc-portfolio x HT-racer x central x absorb), run
# ONT-MAJOR: each ont's 14 configs run back-to-back on one node so within-ont
# time AND mem are clean/comparable. KM_NO_RETRY + high KM_PAR_MEM_GB pin each
# config to its FIXED settings (no reactive downshift confounding the threads
# lever). Excludes the 18 unsolved (handled by probe18). Goal: exact per-ont
# optimum -> generalize to a structural router.
# Submit: sbatch --array=0-49 lattice.sbatch     (50 chunks over 569 onts)
#SBATCH --job-name=km_latt
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=44G
#SBATCH --output=/ibex/scratch/hohndor/km/latt_log/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
cd $KM
export KM_BIN=$KM/engine/target/release/km
export KM_ENGINE_BIN=$KM/engine/target/release/kobayashi-marust
export KM_OFN_BIN=$KM/engine/target/release/ofn
export KM_ELC_BIN=$KM/engine/target/release/elc
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
# pin each config to its fixed settings (isolate the levers)
COMMON="KM_PAR_MEM_GB=38 KM_NO_RETRY=1"

# 14 configs: name|extra-env. absorb is default-ON now; noabsorb uses
# KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0.
CFG=(
"full16|KM_THREADS=16"
"t4|KM_THREADS=4"
"t1|KM_THREADS=1"
"noelc16|KM_NO_ELC_PORTFOLIO=1 KM_THREADS=16"
"noelc_t1|KM_NO_ELC_PORTFOLIO=1 KM_THREADS=1"
"noht16|KM_NO_HT_RACE=1 KM_THREADS=16"
"nocentral_t1|KM_NO_CENTRAL=1 KM_THREADS=1"
"lean16|KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 KM_THREADS=16"
"lean_t1|KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 KM_THREADS=1"
"lowmem_t1|KM_NO_ELC_PORTFOLIO=1 KM_NO_CENTRAL=1 KM_THREADS=1"
"leanmax_t1|KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 KM_NO_CENTRAL=1 KM_THREADS=1"
"noabsorb16|KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_THREADS=16"
"noabsorb_lean_t1|KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 KM_THREADS=1"
"min_t1|KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 KM_NO_CENTRAL=1 KM_THREADS=1"
)
NCHUNK=50
PERCFG_TO=120

ci=${SLURM_ARRAY_TASK_ID:-0}
RESDIR=$KM/latt_res; mkdir -p "$RESDIR" "$KM/latt_log" "$KM/latt_out"
RES=$RESDIR/chunk_${ci}.jsonl
: > "$RES"

mapfile -t ALL < $KM/lattice_onts.txt
li=0
for o in "${ALL[@]}"; do
  if [ $(( li % NCHUNK )) -eq $ci ]; then
    owl=$KM/corpus/ore_ont_${o}.owl
    gold=$KM/gold/konclude__ore_ont_${o}.owl.sig.gz
    [ -f "$owl" ] || { li=$((li+1)); continue; }
    for entry in "${CFG[@]}"; do
      name=${entry%%|*}; cfgenv=${entry#*|}
      OUT=$KM/latt_out/$name; mkdir -p "$OUT"
      # subshell: forks fresh from parent (KM_*_BIN exported), adds COMMON+cfgenv;
      # next config forks from parent again -> no cross-config leakage.
      JSON=$(
        export $COMMON $cfgenv
        python3 $KM/harness/ore_runone.py --reasoner km --ont "$owl" \
          --outdir "$OUT" --timeout $PERCFG_TO --memcap-mb 40000 2>>"$OUT/err.log"
      )
      KMSIG=$OUT/km__ore_ont_${o}.owl.sig.gz
      if [ -f "$KMSIG" ] && [ -f "$gold" ]; then CMP=$(python3 $KM/sig_cmp.py "$KMSIG" "$gold" 2>/dev/null); else CMP="{}"; fi
      python3 - "$JSON" "$CMP" "$name" >> "$RES" <<'PY'
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
    done
  fi
  li=$(( li + 1 ))
done
echo "DONE chunk $ci -> $(wc -l < "$RES") rows"
