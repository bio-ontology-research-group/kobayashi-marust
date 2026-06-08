#!/bin/bash
#SBATCH --job-name=ore_sweep
#SBATCH --partition=debug
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --time=24:00:00
#SBATCH --output=/home/hohndor/bench/ore_jobs/slurm-%A_%a.out
set -u
ID=$(printf %03d "$SLURM_ARRAY_TASK_ID")
JOBDIR=/home/hohndor/bench/ore_jobs
CHUNK=$JOBDIR/chunk_$ID.txt
RES=$JOBDIR/res_$ID.jsonl
OUT=/home/hohndor/bench/ore_out
PY=/home/hohndor/moose/.venv/bin/python
ONTDIR=/home/hohndor/ore2015/pool_sample/files
RUNONE=/home/hohndor/bench/ore_harness/ore_runone.py
mkdir -p "$OUT"
# resume: skip (reasoner,ont) already recorded in this chunk's result file
DONE="$JOBDIR/done_$ID.txt"
"$PY" -c '
import json, os, sys
seen = set()
p = sys.argv[1]
if os.path.exists(p):
    for l in open(p):
        l = l.strip()
        if not l:
            continue
        try:
            r = json.loads(l); seen.add(r["reasoner"] + " " + r["ont"])
        except Exception:
            pass
open(sys.argv[2], "w").write("\n".join(sorted(seen)))
' "$RES" "$DONE"
touch "$RES"
echo "chunk $ID on $(hostname) $(nproc) cores, $(wc -l < "$CHUNK") jobs, $(wc -l < "$DONE") done, start $(date)"
while read -r R ONT; do
  [ -z "${R:-}" ] && continue
  grep -qxF "$R $ONT" "$DONE" && continue
  "$PY" "$RUNONE" --reasoner "$R" --ont "$ONTDIR/$ONT" --outdir "$OUT" \
      --timeout 240 --memcap-mb 20000 >> "$RES" 2>> "$RES.err"
done < "$CHUNK"
echo "DONE chunk $ID $(date)"
