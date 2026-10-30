#!/bin/bash
# usage: scope_run.sh <tag> <km> <list of ontology names file> <parallel> <timeout>
# Runs km classify on every scope input, audits against the references, one TSV row per input.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values
tag=$1; km=$2; list=$3; par=${4:-4}; to=${5:-240}
out=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2/scope/runs/$tag; mkdir -p $out
one() {
  o=$1; d=$out/$o; mkdir -p $d/tmp
  export TMPDIR=$d/tmp OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 KM_THREADS=1 KM_ROUTE=auto KM_TIMING=1
  export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1
  s=$(date +%s.%N)
  timeout -k 5 $to $km classify $S/scope/inputs/$o.owl > $d/taxonomy.raw 2> $d/stderr; rc=$?
  e=$(date +%s.%N); rm -rf $d/tmp
  wall=$(python3 -c "print(round($e-$s,2))")
  dropped=$(python3 -c "import json;d=json.load(open('$d/taxonomy.raw'));print(d.get('dropped',0))" 2>/dev/null)
  route=$(grep -o "route=[a-z_]*" $d/stderr | tail -1)
  accepted=$(grep -o "bounded bridge-first[a-z ()]* accepted\|ABox quotient accepted" $d/stderr | tail -1 | tr ' ' '_')
  verdict=none
  if [ $rc -eq 0 ]; then
    ref=$S/scope/refs/$o; raw=$d/taxonomy.raw
    if [ "${dropped:-0}" != "0" ]; then python3 -c "import json;x=json.load(open('$raw'));x.pop('dropped');json.dump(x,open('$d/stripped','w'))"; raw=$d/stripped; fi
    verdict=$(cd $S/v153tools && python3 canonicalize.py --input $raw --format km-json --signature $ref/signature.tsv --output-prefix $d/canonical --fingerprint-script full_iri_fingerprint.py >/dev/null 2>$d/canon.err && python3 -c "
import json
from compare_taxonomies import compare
a=json.load(open('$d/canonical.validated.json'))
r=[]
for b in ['konclude','hermit','openllet','jfact']:
  try: r.append(b[0]+'='+str(compare(a,json.load(open('$ref/'+b+'.validated.json'))).get('agreement'))[0])
  except Exception: pass
print(','.join(r))" || echo canon-failed)
  fi
  printf "%s\t%s\trc=%s\twall=%s\tdropped=%s\t%s\t%s\t%s\n" "$o" "$tag" "$rc" "$wall" "${dropped:-}" "$route" "$accepted" "$verdict"
}
export -f one; export S out km to tag
xargs -P $par -I{} bash -c 'one {}' < $list > $out.tsv
