#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=04:00:00
#SBATCH --job-name=km-justification-real-pilot
#SBATCH --array=0-1
set -euo pipefail
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
names=(mmo mfomd)
name=${names[$SLURM_ARRAY_TASK_ID]}
out="justification-real-pilot-v2/$name"
mkdir -p "$out/classes"
javac -cp "$runtime/classifier-hermit.jar" -d "$out/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationLibrary.java
python3 - "$name" "$PWD" <<'PY'
import json,sys
from pathlib import Path
name=sys.argv[1];root=Path(sys.argv[2]);p=root/'justification-panel'/name/'modules/q000.tsv'
m=dict(l.split('\t',1) for l in p.read_text().splitlines())
task={'input':str(p.with_suffix('.ofn')),'sub':m['sub'],'super':m['super'],'el':name=='mmo','limits':[1,10],'library':True,'konclude':str(root/'konclude_oracle.py'),'repetition':0,'km':'/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex','runtime':'/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes','classes':str(root/'justification-real-pilot-v2'/name/'classes')}
(root/'justification-real-pilot-v2'/name/'task.json').write_text(json.dumps(task,indent=2)+'\n')
PY
cp justification_run.py "$out/justification_run.py"
sha256sum JustificationBenchmark.java JustificationLibrary.java justification_run.py > "$out/harness.sha256"
python3 "$out/justification_run.py" "$out/task.json" "$out/results"
sha256sum JustificationBenchmark.java justification_run.py > "$out/harness.sha256"
lscpu > "$out/lscpu.txt"
echo JUSTIFICATION_REAL_PILOT_COMPLETE
