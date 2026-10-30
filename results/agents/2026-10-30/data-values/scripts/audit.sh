#!/bin/bash
# usage: audit.sh <outdir> <ontology>; prints agreement per reference; strips 'dropped' into a copy when present
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values
out=$(readlink -f $1); o=$2; ref=$S/refs/$o
raw=$out/taxonomy.raw; tag=""
if python3 -c "import json,sys;d=json.load(open('$raw'));sys.exit(0 if d.get('dropped',0) else 1)" 2>/dev/null; then
  python3 -c "import json;d=json.load(open('$raw'));d.pop('dropped');json.dump(d,open('$out/taxonomy.stripped','w'))"; raw=$out/taxonomy.stripped; tag="(dropped-stripped)"
fi
cd $S/v153tools && python3 canonicalize.py --input $raw --format km-json --signature $ref/signature.tsv --output-prefix $out/canonical --fingerprint-script full_iri_fingerprint.py >/dev/null 2>$out/canon.err || { echo "canon-failed:$(tail -1 $out/canon.err)"; exit 0; }
python3 -c "
import json
from compare_taxonomies import compare
a=json.load(open('$out/canonical.validated.json'))
r=[]
for b in ['konclude','hermit','openllet','jfact']:
  try: r.append(b+'='+str(compare(a,json.load(open('$ref/'+b+'.validated.json'))).get('agreement')))
  except Exception as e: pass
print('$tag'+','.join(r))"
