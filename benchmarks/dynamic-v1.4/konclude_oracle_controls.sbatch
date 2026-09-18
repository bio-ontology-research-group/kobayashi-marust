#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:05:00
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
python3 - <<'PY'
import json, subprocess, gzip
from pathlib import Path
root = Path('konclude-oracle-controls')
root.mkdir(exist_ok=True)
prefix='Prefix(:=<urn:two:>)\nOntology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n'
axioms=['SubClassOf(:A :B)','SubClassOf(:B :D)','SubClassOf(:A :C)','SubClassOf(:C :D)']
for name,active,expected in [('positive',axioms,True),('single-path',axioms[:2],True),('negative',axioms[:1]+axioms[2:3],False)]:
    proc=subprocess.run(['./konclude_oracle.py','incremental-source'],input=json.dumps(dict(op='init',functional_syntax=prefix+'\n'.join(active)+'\n)'))+'\n',text=True,capture_output=True,check=True)
    result=json.loads(proc.stdout)
    assert result['status']=='ok',result
    assert result['result']['consistent'],result
    assert (['urn:two:A','urn:two:D'] in result['result']['subsumptions']) == expected,result
    (root/(name+'.json')).write_text(proc.stdout)
source = Path('inputs/chains/state-000.ofn')
compressed=root/'state-000.ofn.gz'
with gzip.open(compressed,'wb') as out: out.write(source.read_bytes())
(root/'states.txt').write_text(str(compressed.resolve())+'\n')
print('oracle two-path positive, single-path positive, negative: PASS')
PY
python3 konclude_incremental.py /ibex/scratch/hohndor/km/Konclude-official konclude-oracle-controls/states.txt konclude-oracle-controls/gzip-result --reference results/chains/hermit/fresh
