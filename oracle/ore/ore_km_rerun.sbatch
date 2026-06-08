#!/bin/bash
#SBATCH --job-name=ore_kmfix
#SBATCH --partition=debug
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --time=24:00:00
#SBATCH --output=/home/hohndor/bench/ore_jobs/kmfix-%A_%a.out
set -u
ID=$(printf %03d "$SLURM_ARRAY_TASK_ID")
JOBDIR=/home/hohndor/bench/ore_jobs
CHUNK=$JOBDIR/kmchunk_$ID.txt
RES=$JOBDIR/res_km_$ID.jsonl
OUT=/home/hohndor/bench/ore_out_kmfix
PY=/home/hohndor/moose/.venv/bin/python
ONTDIR=/home/hohndor/ore2015/pool_sample/files
RUNONE=/home/hohndor/bench/ore_harness/ore_runone.py
# KM re-run uses the FIXED parallel binary (audit fixes H1/H2/M1/M2/L1/L2).
export KM_ENGINE_BIN=/home/hohndor/bench/km/kobayashi-marust-par-fixed
mkdir -p "$OUT"
: > "$RES"
echo "kmfix chunk $ID on $(hostname) $(nproc) cores, $(wc -l < "$CHUNK") onts, start $(date)"
while read -r ONT; do
  [ -z "${ONT:-}" ] && continue
  "$PY" "$RUNONE" --reasoner km --ont "$ONTDIR/$ONT" --outdir "$OUT" \
      --timeout 240 --memcap-mb 20000 >> "$RES" 2>> "$RES.err"
done < "$CHUNK"
echo "DONE kmfix $ID $(date)"
