#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=01:00:00
#SBATCH --job-name=km-justification-panel
#SBATCH --array=0-5
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
source_root=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged
names=(mmo hao vto mfomd to uberon)
name=${names[$SLURM_ARRAY_TASK_ID]}
out="justification-panel/$name"
mkdir -p "$out/classes"
javac -cp "$runtime/classifier-hermit.jar" -d "$out/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationPanel.java
opts=(-XX:ActiveProcessorCount=1 -Xmx16g -Delk.reasoner.number_of_workers=1)
for reasoner in hermit jfact; do
 factory=org.semanticweb.HermiT.ReasonerFactory
 if [ "$reasoner" = jfact ]; then factory=uk.ac.manchester.cs.jfact.JFactFactory; fi
 mkdir -p "$out/$reasoner"
 set +e
 /usr/bin/time -v -o "$out/$reasoner/process.time" timeout -k 5 600 java "${opts[@]}" -cp "$out/classes:$runtime/classifier-$reasoner.jar" org.kmbenchmark.JustificationPanel candidates "$factory" "$source_root/$name.ofn" "$out/$reasoner" >"$out/$reasoner/stdout.log" 2>"$out/$reasoner/stderr.log"
 rc=$?
 set -e
 echo "$rc" > "$out/$reasoner/exit-code"
done
python3 - "$out" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1])
for r in ['hermit','jfact']:
 if not (p/r/'COMPLETE').exists(): raise SystemExit('candidate classification incomplete: '+r)
a=(p/'hermit/taxonomy.tsv').read_bytes(); b=(p/'jfact/taxonomy.tsv').read_bytes()
if a!=b: raise SystemExit('independent taxonomy disagreement')
queries=(p/'hermit/candidates.tsv').read_text().splitlines()[:5]
(p/'queries.tsv').write_text('\n'.join(queries)+'\n')
PY
timeout -k 5 600 java "${opts[@]}" -cp "$out/classes:$runtime/classifier-hermit.jar" org.kmbenchmark.JustificationPanel modules "$out/queries.tsv" "$source_root/$name.ofn" "$out/modules" >"$out/modules.stdout" 2>"$out/modules.stderr"
sha256sum "$source_root/$name.ofn" "$out/queries.tsv" "$out"/modules/*.ofn *.java > "$out/hashes.txt"
echo JUSTIFICATION_PANEL_COMPLETE
