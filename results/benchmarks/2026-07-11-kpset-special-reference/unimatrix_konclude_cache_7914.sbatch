#!/bin/bash
#SBATCH --job-name=kon-cache-7914
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --output=/home/hohndor/bench/ore_jobs/kon-cache-7914-%j.out

set -u

root="$HOME/bench"
prefix="$root/ore_jobs/kon-cache-7914-${SLURM_JOB_ID}"
binary="$root/reasoners/Konclude-cache-debug2"
input="$HOME/ore2015/pool_sample/files/ore_ont_7914.owl"

echo "BEGIN host=$(hostname) date=$(date -Is) sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
/usr/bin/time -v -o "$prefix.time" \
  /usr/bin/timeout 300 /usr/bin/env \
    LD_LIBRARY_PATH="$root/reasoners" KCOMPDBG=UBERON_0003657 \
    "$binary" classification -w 16 -v -i "$input" -o "$prefix.owl" \
    >"$prefix.stdout" 2>"$prefix.stderr"
rc=$?
echo "rc=$rc"
echo "CACHE-TRACE"
/usr/bin/grep -E 'KCOMPDBG activate|KCACHECON|KCOMPDBG task-fixpoint' "$prefix.stderr" || true
exit "$rc"
