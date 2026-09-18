#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=00:08:00
#SBATCH --job-name=km-v143-rc2
set -euo pipefail
root=/ibex/scratch/hohndor/km/v143-harness-20260918
test -f "$root/STAGE-COMPLETE"
cd "$root"
sha256sum -c harness-binary.sha256
chunk=000
out="$root/targeted-v143-rc2/$chunk"
mkdir -p "$out"
export HARNESS_OUT_DIR="$out/output"
export KM140_BIN=/ibex/scratch/hohndor/km/v143-harness-20260918/km-candidate-v143-rc2
export TMPDIR="$out/tmp"
mkdir -p "$TMPDIR"
printf 'SLURM_JOB_ID=%s\nSLURM_ARRAY_JOB_ID=%s\nSLURM_ARRAY_TASK_ID=%s\nKM140_BIN=%s\n' "$SLURM_JOB_ID" "$SLURM_ARRAY_JOB_ID" "$SLURM_ARRAY_TASK_ID" "$KM140_BIN" > "$out/environment.txt"
lscpu > "$out/lscpu.txt"
"$root/target/release/owl-reasoner-harness" run \
 --corpus "$root/corpus/pool_sample/files" --only "$root/targeted-3215.txt" \
 --reasoner "$root/source/wrappers/run-km-v140.sh" --args '{}' \
 --cap-secs 240 --threads 1 --mem-mb 20480 --out "$out/results.jsonl" \
 > "$out/driver.stdout" 2> "$out/driver.stderr"
touch "$out/COMPLETE"

python3 - "$out/results.jsonl" <<'CHECK'
import sys,json
rows=[json.loads(l)for l in open(sys.argv[1])];cases=[r for r in rows if r.get('kind')=='case']
assert len(cases)==1 and cases[0]['ont']=='ore_ont_3215' and cases[0]['outcome']=='ok', cases
CHECK
