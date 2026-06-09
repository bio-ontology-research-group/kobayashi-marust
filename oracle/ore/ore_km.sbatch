#!/bin/bash
#SBATCH --job-name=ore_kmcur2
#SBATCH --partition=debug
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --time=24:00:00
#SBATCH --output=/home/hohndor/bench/ore_jobs/kmcur2-%A_%a.out
set -u
ID=$(printf %03d "$SLURM_ARRAY_TASK_ID")
JOBDIR=/home/hohndor/bench/ore_jobs
CHUNK=$JOBDIR/kmchunk_$ID.txt
RES=$JOBDIR/res_kmcur2_$ID.jsonl
OUT=/home/hohndor/bench/ore_out_kmcur2
PY=/home/hohndor/moose/.venv/bin/python
ONTDIR=/home/hohndor/ore2015/pool_sample/files
RUNONE=/home/hohndor/bench/ore_harness/ore_runone.py
# current branch payg-strategy HEAD: audit fixes + e0f6e34 forward-subsumption
# Elim-gap completeness fix + router/tableau perf work.
export KM_ENGINE_BIN=/home/hohndor/bench/km/kobayashi-marust-par-cur
mkdir -p "$OUT"
: > "$RES"
echo "kmcur chunk $ID on $(hostname) $(nproc) cores, $(wc -l < "$CHUNK") onts, start $(date)"
while read -r ONT; do
  [ -z "${ONT:-}" ] && continue
  "$PY" "$RUNONE" --reasoner km --ont "$ONTDIR/$ONT" --outdir "$OUT" \
      --timeout 240 --memcap-mb 20000 >> "$RES" 2>> "$RES.err"
done < "$CHUNK"
echo "DONE kmcur $ID $(date)"
