#!/bin/bash
# refcmp.sh LINES_OUT REFDIR WORKDIR : canonicalize a --lines output and compare it with the pinned references.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-abox-probes/results/agents/2026-11-02/bridge-abox-probes
T=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values/v153tools
out=$1; ref=$2; d=$3; mkdir -p $d
python3 -I $S/tools/lines2json.py $out $d/taxonomy.json
cd $T && python3 canonicalize.py --input $d/taxonomy.json --format km-json --signature $ref/signature.tsv --output-prefix $d/canonical --fingerprint-script full_iri_fingerprint.py > $d/canon.out 2> $d/canon.err || { echo canon-failed; exit 1; }
python3 -c "
import json
from compare_taxonomies import compare
a=json.load(open('$d/canonical.validated.json'))
r=[]
for b in ['konclude','hermit','openllet','jfact']:
  try: r.append(b+'='+str(compare(a,json.load(open('$ref/'+b+'.validated.json'))).get('agreement')))
  except FileNotFoundError: pass
  except Exception as e: r.append(b+'=error:'+str(e)[:60])
print(' '.join(r))"
