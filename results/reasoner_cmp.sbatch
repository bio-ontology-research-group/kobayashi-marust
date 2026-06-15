#!/bin/bash
# Side-by-side ORE-2015 reasoner comparison on IBEX.
# One ontology per array task; all reasoners run SEQUENTIALLY on the SAME node
# (same hardware, same time/mem ceiling) so wall/peak are directly comparable.
# Generous ceiling (600 s / 56 GB) + recorded actual wall/peak => post-hoc we can
# answer "with what time/mem limits does reasoner X solve ORE".
#SBATCH --job-name=rcmp
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=1:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/cmp/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km

# --- JVM reasoners: bundled Temurin 8 (matches validated gold runs) + big heap ---
export BENCH_JAVA=$KM/bench/jdk8u492-b09/bin/java
export BENCH_XMX=-Xmx56g

# --- KM production config (the improved, deployed pipeline: auto-router on) ---
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
export KM_TAB_RACE=1
export KM_TAB_BIN=$KM/engine/target/release/tableau_cli
export KM_THREADS=16

TIMEOUT=${TIMEOUT:-600}
MEMCAP=${MEMCAP:-56000}
REASONERS=${REASONERS:-"konclude elk hermit km"}

mapfile -t ONTS < $KM/prof/cmp_onts.txt
ID=${SLURM_ARRAY_TASK_ID:-0}
ONT=${ONTS[$ID]}
ONTFILE=$KM/corpus/ore_ont_${ONT}.owl

OUT=$KM/cmp_out;  mkdir -p "$OUT"
RESDIR=$KM/cmp_res; mkdir -p "$RESDIR"
RES=$RESDIR/ont_${ONT}.jsonl
: > "$RES"

echo "=== ont $ONT  host=$(hostname)  $(date +%T) ==="
for R in $REASONERS; do
  t0=$SECONDS
  python3 $KM/harness/ore_runone.py --reasoner $R --ont "$ONTFILE" \
      --outdir "$OUT" --timeout $TIMEOUT --memcap-mb $MEMCAP 2>/dev/null >> "$RES"
  echo "  $R done in $(( SECONDS - t0 ))s"
done

# gold comparison (Konclude 300s/16GB gold sig is the reference)
GSIG=$KM/gold/konclude__ore_ont_${ONT}.owl.sig.gz
for R in $REASONERS; do
  SIG=$OUT/${R}__ore_ont_${ONT}.owl.sig.gz
  if [ -f "$SIG" ] && [ -f "$GSIG" ]; then
    if cmp -s <(zcat "$SIG" 2>/dev/null) <(zcat "$GSIG" 2>/dev/null); then G=MATCH; else G=DIFF; fi
  else G=NOSIG; fi
  echo "{\"gold_cmp\": \"$R\", \"ont\": \"$ONT\", \"gold\": \"$G\"}" >> "$RES"
done
echo "DONE ont $ONT"
