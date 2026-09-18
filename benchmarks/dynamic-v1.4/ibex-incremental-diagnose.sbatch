#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:10:00
#SBATCH --job-name=km-incremental-diagnose
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
python3 - <<'PY'
import json,subprocess
from pathlib import Path
root=Path('abox-diagnosis-v2');root.mkdir(exist_ok=False)
binary='/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex'
source=Path('inputs/abox/state-001.ofn').read_text()
variants={'prefix':source,'full-urn':source.replace('Prefix(:=<urn:km:control:>)','').replace(':A','<urn:km:control:A>').replace(':B','<urn:km:control:B>').replace(':a','<urn:km:control:a>'),'full-http':source.replace('Prefix(:=<urn:km:control:>)','').replace(':A','<http://example.org/A>').replace(':B','<http://example.org/B>').replace(':a','<http://example.org/a>')}
for name,text in variants.items():
 p=root/(name+'.ofn');p.write_text(text)
 for action,args,data in [('frontend',['ofn',str(p)],None),('classify',['classify',str(p)],None),('incremental',['incremental-source'],json.dumps({'op':'init','functional_syntax':text})+'\n')]:
  r=subprocess.run([binary,*args],input=data,text=True,capture_output=True,timeout=120)
  (root/(name+'.'+action+'.json')).write_text(r.stdout)
  (root/(name+'.'+action+'.stderr')).write_text(r.stderr)
  print(name,action,r.returncode,flush=True)
  if r.returncode != 0: raise RuntimeError((name,action,r.stderr))
PY
