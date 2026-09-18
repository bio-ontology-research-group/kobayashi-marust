#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:30:00
#SBATCH --job-name=km-justification-external-probe
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
out=justification-diagnose-mfomd/external
mkdir -p "$out/classes"
javac -cp /ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar -d "$out/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationLibrary.java
python3 - "$PWD" <<'PY'
import json,sys
from pathlib import Path
root=Path(sys.argv[1]);task=json.loads((root/'justification-real-pilot-v2/mfomd/task.json').read_text())
task.update(input=str(root/'justification-diagnose-mfomd/observed-0000.ofn'),limits=[1],arms=['hermit-common','jfact-common','openllet-common','hermit-library'],classes=str(root/'justification-diagnose-mfomd/external/classes'))
(root/'justification-diagnose-mfomd/external/task.json').write_text(json.dumps(task)+'\n')
PY
cp justification_run.py "$out/justification_run.py"
python3 "$out/justification_run.py" "$out/task.json" "$out/results"
echo JUSTIFICATION_EXTERNAL_PROBE_COMPLETE
