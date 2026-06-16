#!/bin/bash
# Side-by-side ORE-2015 reasoner comparison on IBEX, KM = the post-integration
# LIVE config (avg-performance winner): new binary + KM_ABSORB + KM_ABSORB_PORTFOLIO
# + seq auto-route, NO KM_TAB_RACE (the tableau race lost on median wall: 0.25->0.33
# for a single +ont, so it is dropped from the default per the avg-time/mem metric).
# All four reasoners run SEQUENTIALLY on the SAME node per ont => wall/peak directly
# comparable. Fresh result dir (cmp2_*) so the prior baseline (47530284) is preserved.
#SBATCH --job-name=rcmp2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/cmp2/slurm-%A_%a.out
#SBATCH --array=0-29
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km

# --- JVM reasoners: bundled Temurin 8 (matches validated gold runs) + big heap ---
export BENCH_JAVA=$KM/bench/jdk8u492-b09/bin/java
export BENCH_XMX=-Xmx56g

# --- KM LIVE config (avg-performance winner) ---
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
export KM_PAR_MEM_GB=44
export KM_ABSORB=1
export KM_ABSORB_PORTFOLIO=1
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
export KM_THREADS=16
# NO KM_TAB_RACE / KM_SEQ_ORDER -> engine auto-routes seq by DISJ_INT.

TIMEOUT=${TIMEOUT:-600}
MEMCAP=${MEMCAP:-56000}
REASONERS=${REASONERS:-"konclude elk hermit km"}

mapfile -t ONTS < $KM/prof/cmp_onts.txt
N=${#ONTS[@]}
OUT=$KM/cmp2_out;  mkdir -p "$OUT"
RESDIR=$KM/cmp2_res; mkdir -p "$RESDIR"

for ((idx=SLURM_ARRAY_TASK_ID; idx<N; idx+=30)); do
  ONT=${ONTS[$idx]}
  ONTFILE=$KM/corpus/ore_ont_${ONT}.owl
  [ -f "$ONTFILE" ] || continue
  RES=$RESDIR/ont_${ONT}.jsonl
  : > "$RES"
  echo "=== ont $ONT  host=$(hostname)  $(date +%T) ==="
  for R in $REASONERS; do
    t0=$SECONDS
    python3 $KM/harness/ore_runone.py --reasoner $R --ont "$ONTFILE" \
        --outdir "$OUT" --timeout $TIMEOUT --memcap-mb $MEMCAP 2>/dev/null >> "$RES"
    echo "  $R done in $(( SECONDS - t0 ))s"
  done
  GSIG=$KM/gold/konclude__ore_ont_${ONT}.owl.sig.gz
  for R in $REASONERS; do
    SIG=$OUT/${R}__ore_ont_${ONT}.owl.sig.gz
    if [ -f "$SIG" ] && [ -f "$GSIG" ]; then
      if cmp -s <(zcat "$SIG" 2>/dev/null) <(zcat "$GSIG" 2>/dev/null); then G=MATCH; else G=DIFF; fi
    else G=NOSIG; fi
    echo "{\"gold_cmp\": \"$R\", \"ont\": \"$ONT\", \"gold\": \"$G\"}" >> "$RES"
  done
done
echo "DONE task ${SLURM_ARRAY_TASK_ID} $(date +%T)"
