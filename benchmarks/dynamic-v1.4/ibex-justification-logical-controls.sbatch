#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=02:00:00
#SBATCH --array=0-1
#SBATCH --job-name=km-justification-logical
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
names=(unsatisfiable inconsistent)
name=${names[$SLURM_ARRAY_TASK_ID]}
export CONTROL_NAME="$name"
mkdir -p "justification-logical-controls/$name/classes"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
javac -cp "$runtime/classifier-hermit.jar" -d "justification-logical-controls/$name/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationLibrary.java
python3 - <<'PY'
from pathlib import Path
import os,json,hashlib
root=Path.cwd();name=os.environ['CONTROL_NAME'];out=root/'justification-logical-controls'/name
if name=='unsatisfiable':
 axioms=['SubClassOf(<http://example.org/A> <http://example.org/B>)','SubClassOf(<http://example.org/A> <http://example.org/C>)','DisjointClasses(<http://example.org/B> <http://example.org/C>)']
 sub='http://example.org/A';sup='http://www.w3.org/2002/07/owl#Nothing'
else:
 axioms=['ClassAssertion(<http://example.org/B> <http://example.org/a>)','ClassAssertion(<http://example.org/C> <http://example.org/a>)','DisjointClasses(<http://example.org/B> <http://example.org/C>)']
 sub='http://www.w3.org/2002/07/owl#Thing';sup='http://www.w3.org/2002/07/owl#Nothing'
source=out/'input.ofn';source.write_text('Ontology(\n'+'\n'.join(axioms)+'\n)\n')
task={'ontology':name,'query_id':'control','track':'analytic','input':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'sub':sub,'super':sup,'el':name=='unsatisfiable','limits':[1,10,100],'library':True,'repetition':0,'warmup':True,'km':'/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex','konclude':str(root/'konclude_oracle.py'),'runtime':'/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes','classes':str(out/'classes')}
(out/'task.json').write_text(json.dumps(task,indent=2)+'\n')
PY
python3 justification_run.py "justification-logical-controls/$name/task.json" "justification-logical-controls/$name/results"
sha256sum *.java justification_run.py konclude_oracle.py konclude_incremental.py > "justification-logical-controls/$name/harness.sha256"
echo JUSTIFICATION_LOGICAL_CONTROL_COMPLETE
