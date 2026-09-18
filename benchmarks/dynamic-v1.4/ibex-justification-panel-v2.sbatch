#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:40:00
#SBATCH --job-name=km-justification-panel-v2
#SBATCH --array=0-5
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
source_root=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged
names=(mmo hao vto mfomd to uberon)
name=${names[$SLURM_ARRAY_TASK_ID]}
out="justification-panel-v2/$name"
mkdir -p "$out/classes" "$out/hermit" "$out/jfact"
javac -cp "$runtime/classifier-hermit.jar" -d "$out/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationPanel.java
opts=(-XX:ActiveProcessorCount=1 -Xmx16g -Delk.reasoner.number_of_workers=1)
set +e
/usr/bin/time -v -o "$out/hermit/process.time" timeout -k 5 600 java "${opts[@]}" -cp "$out/classes:$runtime/classifier-hermit.jar" org.kmbenchmark.JustificationPanel sample org.semanticweb.HermiT.ReasonerFactory "$source_root/$name.ofn" "$out/hermit" >"$out/hermit/stdout.log" 2>"$out/hermit/stderr.log"
rc=$?
set -e
echo "$rc" > "$out/hermit/exit-code"
[ "$rc" -eq 0 ] || exit "$rc"
cp "$out/hermit/queries.tsv" "$out/queries.tsv"
set +e
/usr/bin/time -v -o "$out/jfact/process.time" timeout -k 5 600 java "${opts[@]}" -cp "$out/classes:$runtime/classifier-jfact.jar" org.kmbenchmark.JustificationPanel validate uk.ac.manchester.cs.jfact.JFactFactory "$source_root/$name.ofn" "$out/jfact" "$out/queries.tsv" >"$out/jfact/stdout.log" 2>"$out/jfact/stderr.log"
rc=$?
set -e
echo "$rc" > "$out/jfact/exit-code"
[ "$rc" -eq 0 ] || exit "$rc"
timeout -k 5 600 java "${opts[@]}" -cp "$out/classes:$runtime/classifier-hermit.jar" org.kmbenchmark.JustificationPanel modules "$out/queries.tsv" "$source_root/$name.ofn" "$out/modules" >"$out/modules.stdout" 2>"$out/modules.stderr"
sha256sum "$source_root/$name.ofn" "$out/queries.tsv" "$out"/modules/*.ofn JustificationPanel.java > "$out/hashes.txt"
echo JUSTIFICATION_PANEL_V2_COMPLETE
