#!/bin/bash
#SBATCH --job-name=kmrtpar
#SBATCH --partition=debug
#SBATCH --exclude=unimatrix,node001
#SBATCH --cpus-per-task=8
#SBATCH --mem=22G
#SBATCH --time=24:00:00
#SBATCH --output=/home/hohndor/bench/ore_jobs/kmrtpar-%A_%a.out
set -u
: "${KM_ROUTER_MODE:?set KM_ROUTER_MODE (default|cb|ht)}"
ID=$(printf %03d "$SLURM_ARRAY_TASK_ID")
CHUNK=/home/hohndor/bench/ore_jobs/kmchunk_$ID.txt
OUTDIR=/home/hohndor/bench/ore_out_router_${KM_ROUTER_MODE}
RES=/home/hohndor/bench/ore_jobs/res_router_${KM_ROUTER_MODE}_$ID.jsonl
# rough-but-fast: pack many tasks per node; cap threads/mem so they coexist.
export KM_ROUTER_MODE OUTDIR HT_TIMEOUT=120 MEMCAP_MB=20000 KM_THREADS=8 KM_PAR_MEM_GB=16
mkdir -p "$OUTDIR"
: > "$RES"
while read -r ONT; do
  [ -z "${ONT:-}" ] && continue
  python3 /home/hohndor/bench/ore_harness/router_runone.py "$ONT" >> "$RES" 2>> "$RES.err"
done < "$CHUNK"
echo "DONE kmrtpar $KM_ROUTER_MODE $ID $(date)"
