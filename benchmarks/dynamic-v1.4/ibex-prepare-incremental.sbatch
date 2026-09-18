#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=02:00:00
#SBATCH --array=0-17%4
#SBATCH --job-name=km-incremental-traces
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar
index=$((SLURM_ARRAY_TASK_ID / 3))
changes=(1 10 100)
n=${changes[$((SLURM_ARRAY_TASK_ID % 3))]}
read -r id expected ontology < <(python3 - "$index" <<'PY'
import csv,sys
r=list(csv.DictReader(open('incremental-panel.tsv'),delimiter='\t'))[int(sys.argv[1])]
print(r['id'],r['sha256'],r['path'])
PY
)
test "$(sha256sum "$ontology" | cut -d' ' -f1)" = "$expected"
out="$DYNAMIC_ROOT/inputs/$id-n$n"
mkdir -p "$out/classes"
javac -cp "$runtime" -d "$out/classes" DynamicBenchmark.java
java -XX:ActiveProcessorCount=1 -Xmx16g -cp "$out/classes:$runtime" org.kmbenchmark.DynamicBenchmark prepare "$ontology" "$out" 250 "$n" 20260917 gzip
head -6 "$out/states.txt" > "$out/pilot-states.txt"
find "$out" -name '*.ofn.gz' -print0 | sort -z | xargs -0 sha256sum > "$out/SHA256SUMS"
sha256sum "$ontology" "$runtime" DynamicBenchmark.java incremental-panel.tsv > "$out/provenance.sha256"
printf 'job=%s\nstates=251\nseed=20260917\nchanges=%s\n' "$SLURM_JOB_ID" "$n" > "$out/COMPLETE"
