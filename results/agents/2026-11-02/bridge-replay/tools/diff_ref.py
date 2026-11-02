#!/usr/bin/env python3
"""Compare a `km classify --lines` output with the pinned references.

usage: diff_ref.py ONT_NUMBER LINES_FILE WORKDIR
Converts --lines to the km-json shape, canonicalises it with the pinned
canonicalize.py against the reference signature, and compares the result with
konclude/openllet/jfact validated records via compare_taxonomies.py.
Prints one JSON line.
"""
import json, subprocess, sys
from pathlib import Path

ROOT = Path('/mnt/data2/workspaces/leechuck/software/kobayashi-marust')
TOOLS = ROOT / '.work/v152-correctness-1920'
ont, lines_file, work = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
rows = json.loads((TOOLS / 'full-candidate-inputs-ws.json').read_text())['inputs']
ref = None
for row in rows:
    if Path(row.get('reference_directory', '')).name == 'ore_ont_' + ont:
        ref = Path(row['reference_directory'])
if ref is None:
    print(json.dumps({'ontology': ont, 'status': 'no_reference'})); sys.exit(0)
consistent, dropped, subs, unsat = None, None, [], []
for line in lines_file.read_text().splitlines():
    f = line.split('\t') if '\t' in line else line.split(' ')
    if f[0] == 'CONSISTENT': consistent = f[1] == '1'
    elif f[0] == 'DROPPED': dropped = int(f[1])
    elif f[0] == 'SUB': subs.append([f[1], f[2]])
    elif f[0] == 'UNSAT': unsat.append(f[1])
    elif f[0] == 'APPROXIMATE': dropped = -1
if consistent is None or dropped != 0:
    print(json.dumps({'ontology': ont, 'status': 'no_answer', 'dropped': dropped})); sys.exit(0)
work.mkdir(parents=True, exist_ok=True)
raw = work / ('ore_ont_%s.km.json' % ont)
raw.write_text(json.dumps({'consistent': consistent, 'subsumptions': subs, 'unsatisfiable': unsat}))
prefix = work / ('ore_ont_%s.km' % ont)
run = subprocess.run([sys.executable, str(TOOLS / 'canonicalize.py'), '--input', str(raw), '--format', 'km-json',
                      '--signature', str(ref / 'signature.tsv'), '--output-prefix', str(prefix),
                      '--fingerprint-script', str(TOOLS / 'full_iri_fingerprint.py')], capture_output=True, text=True)
if run.returncode != 0:
    print(json.dumps({'ontology': ont, 'status': 'canonicalize_failed', 'err': run.stderr[-500:]})); sys.exit(0)
out = {'ontology': ont, 'status': 'compared', 'subsumption_lines': len(subs), 'unsat': len(unsat)}
for name in ('konclude', 'openllet', 'jfact'):
    r = ref / ('%s.validated.json' % name)
    if not r.exists():
        out[name] = 'missing'; continue
    c = subprocess.run([sys.executable, str(TOOLS / 'compare_taxonomies.py'), str(prefix) + '.validated.json', str(r)],
                       capture_output=True, text=True)
    try:
        out[name] = json.loads(c.stdout)['status']
    except Exception:
        out[name] = 'compare_failed: ' + (c.stderr or c.stdout)[-200:]
print(json.dumps(out))
