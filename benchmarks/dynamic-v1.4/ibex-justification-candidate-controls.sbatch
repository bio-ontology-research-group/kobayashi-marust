#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=02:00:00
#SBATCH --array=0-4
#SBATCH --job-name=km-justification-candidate
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
CANDIDATE_ROOT=/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/abox-candidate-v1
export CANDIDATE_BIN="$CANDIDATE_ROOT/km.ibex"
CANDIDATE_SHA=$(python3 - "$CANDIDATE_ROOT" <<'PY_CHECK'
import hashlib,sys
from pathlib import Path
root=Path(sys.argv[1]);expected='9a77671d75ed4d72e5cf4786610da1daeedb4054058e9b7c13177d10e691204d'
rows=[line.split('\t',1) for line in (root/'build-receipt.tsv').read_text().splitlines()];receipt=dict(rows)
assert len(rows)==len(receipt), 'duplicate receipt fields'
assert receipt['Z']=='complete' and receipt['slurm_job_id']=='51982442'
assert receipt['source_archive_sha256']==expected
assert hashlib.sha256((root/'source.tgz').read_bytes()).hexdigest()==expected
actual=hashlib.sha256((root/'km.ibex').read_bytes()).hexdigest()
assert receipt['binary_sha256']==actual
print(actual)
PY_CHECK
)
export CANDIDATE_SHA
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
names=(unsatisfiable inconsistent two-paths noise negative)
name=${names[$SLURM_ARRAY_TASK_ID]}
export CONTROL_NAME="$name"
mkdir -p "justification-candidate-controls/$name/classes"
cp "$CANDIDATE_ROOT/build-receipt.tsv" "justification-candidate-controls/$name/candidate-build-receipt.tsv"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
javac -cp "$runtime/classifier-hermit.jar" -d "justification-candidate-controls/$name/classes" DynamicBenchmark.java JustificationBenchmark.java JustificationLibrary.java
python3 - <<'PY'
from pathlib import Path
import os,json,hashlib
root=Path.cwd();name=os.environ['CONTROL_NAME'];out=root/'justification-candidate-controls'/name
if name=='unsatisfiable':
 axioms=['SubClassOf(<http://example.org/A> <http://example.org/B>)','SubClassOf(<http://example.org/A> <http://example.org/C>)','DisjointClasses(<http://example.org/B> <http://example.org/C>)']
 sub='http://example.org/A';sup='http://www.w3.org/2002/07/owl#Nothing'
elif name=='inconsistent':
 axioms=['ClassAssertion(<http://example.org/B> <http://example.org/a>)','ClassAssertion(<http://example.org/C> <http://example.org/a>)','DisjointClasses(<http://example.org/B> <http://example.org/C>)']
 sub='http://www.w3.org/2002/07/owl#Thing';sup='http://www.w3.org/2002/07/owl#Nothing'
else:
 axioms=['SubClassOf(<http://example.org/A> <http://example.org/B>)','SubClassOf(<http://example.org/B> <http://example.org/D>)','SubClassOf(<http://example.org/A> <http://example.org/C>)','SubClassOf(<http://example.org/C> <http://example.org/D>)']
 if name=='noise':axioms += [f'SubClassOf(<http://example.org/Noise{i}> <http://example.org/Noise{i+1}>)' for i in range(30)]
 if name=='negative':axioms=['SubClassOf(<http://example.org/A> <http://example.org/B>)','Declaration(Class(<http://example.org/D>))']
 sub='http://example.org/A';sup='http://example.org/D'
source=out/'input.ofn';source.write_text('Ontology(\n'+'\n'.join(axioms)+'\n)\n')
task={'ontology':name,'query_id':'control','track':'analytic','input':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'sub':sub,'super':sup,'el':name=='unsatisfiable','limits':[1,10,100],'library':True,'repetition':0,'warmup':True,'arms':['km-native','km-common'],'km':os.environ['CANDIDATE_BIN'],'km_sha256':os.environ['CANDIDATE_SHA'],'konclude':str(root/'konclude_oracle.py'),'runtime':'/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes','classes':str(out/'classes')}
(out/'task.json').write_text(json.dumps(task,indent=2)+'\n')
PY
python3 justification_run.py "justification-candidate-controls/$name/task.json" "justification-candidate-controls/$name/results"
sha256sum *.java justification_run.py konclude_oracle.py konclude_incremental.py > "justification-candidate-controls/$name/harness.sha256"
echo JUSTIFICATION_CANDIDATE_CONTROL_COMPLETE
