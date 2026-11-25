#!/bin/bash
# H2 item 0: the witness row on ore_ont_580 with owl:Thing and owl:Nothing requested must
# certify no row `A ⋢ owl:Thing`. usage: builtin580.sh BIN OUTDIR
set -e
B=$1; D=$2; C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
H=$(cd "$(dirname "$0")" && pwd); mkdir -p "$D"; cd "$D"
$B --procedure sroiq-hint --witness-route --print-index $C/ore_ont_580.owl > 580.idx
$B --procedure sroiq-hint --witness-route --print-clauses $C/ore_ont_580.owl > 580.cls
python3 -c "
import sys; sys.path.insert(0, '$H/..'); import nf, hintcheck
from driver5 import build
h, form, st = build(nf.from_route(open('580.idx').read(), open('580.cls').read()))
hintcheck.write(h, '580.hint', None)"
python3 - <<'PY'
cls = {int(l.split()[1]): l.split()[2] for l in open('580.idx') if l.startswith('concept ') and not l.split()[2].startswith('urn:')}
seen = {}
for l in open('580.hint'):
    w = l.split()
    if w and w[0] == 'ty':
        for x in map(int, w[2:]):
            if x in cls: seen.setdefault(x, int(w[1]))
open('580.wt', 'w').write(''.join('witness %s %d\n' % (cls[x], e) for x, e in seen.items()))
open('580.classes', 'w').write('http://www.w3.org/2002/07/owl#Thing\n' + '\n'.join(cls.values()) + '\nhttp://www.w3.org/2002/07/owl#Nothing\n')
PY
$B --procedure sroiq-hint --witness 580.wt --classes 580.classes --hint 580.hint $C/ore_ont_580.owl > 580.out
python3 -c "
import json; rows = [json.loads(l) for l in open('580.out')]
bad = [r for r in rows if 'http://www.w3.org/2002/07/owl#Thing' in r.get('nonsub', [])]
print('rows certifying A not below owl:Thing:', len(bad)); assert not bad"
