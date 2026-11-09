#!/bin/bash
# one ORE input per task: KM_BIN, KM_TAGRUN; array index selects (input, rep)
#SBATCH --job-name=km155-nc-run
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:15:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030/slurm/run-%A_%a.out
set -uo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030
C=/ibex/scratch/hohndor/km/v143-harness-20260918/corpus/pool_sample/files
inputs=(ore_ont_9800 ore_ont_10874)
i=${SLURM_ARRAY_TASK_ID}
n=${inputs[$((i % 2))]}; rep=$((i / 2))
out=$ROOT/out/${KM_TAGRUN}/$n.rep$rep; /usr/bin/mkdir -p "$out"
export TMPDIR=$ROOT/tmp/${SLURM_ARRAY_JOB_ID}_$i; /usr/bin/mkdir -p "$TMPDIR"
for v in $(env | grep -o '^KM_[A-Z_0-9]*' | grep -v -E '^KM_(BIN|TAGRUN)$'); do unset $v; done
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1
s=$(date +%s.%N)
KM_TIMING=1 /usr/bin/timeout -s KILL 240 "$KM_BIN" classify --lines "$C/$n.owl" > "$out/out.txt" 2> "$out/err.txt"
rc=$?; e=$(date +%s.%N)
grep -E '^(SUB|UNSAT|CONSISTENT)' "$out/out.txt" | sort | gzip > "$out/sig.gz"; rm -f "$out/out.txt"
echo -e "$n\t$KM_TAGRUN\t$rep\t$rc\t$(echo "$e - $s" | bc)\t$(hostname)\t$(nproc)" > "$out/time.tsv"
/usr/bin/rm -rf "$TMPDIR"
