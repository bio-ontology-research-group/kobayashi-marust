#!/bin/bash
#SBATCH --job-name=km-flat-declines
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/declines-%j.out

set -euo pipefail
/usr/bin/python3 - <<'PY'
import collections, json, re

ids = [868, 8737, 16744, 1559, 14042, 15059]
class_decl = re.compile(r'^Declaration\(Class\(<[^<>\s]+>\)\)$')
role_decl = re.compile(r'^Declaration\(ObjectProperty\(<[^<>\s]+>\)\)$')
named_sub = re.compile(r'^SubClassOf\(<[^<>\s]+> <[^<>\s]+>\)$')
rbox = [
    re.compile(r'^SubObjectPropertyOf\(<[^<>\s]+> <[^<>\s]+>\)$'),
    re.compile(r'^InverseObjectProperties\(<[^<>\s]+> <[^<>\s]+>\)$'),
    re.compile(r'^SymmetricObjectProperty\(<[^<>\s]+>\)$'),
    re.compile(r'^TransitiveObjectProperty\(<[^<>\s]+>\)$'),
]
for oid in ids:
    counts = collections.Counter()
    first = {}
    path = f'/ibex/scratch/hohndor/km/corpus/ore_ont_{oid}.owl'
    with open(path, encoding='utf-8') as source:
        for number, raw in enumerate(source, 1):
            line = raw.strip()
            if not line or line.startswith('Prefix(') or line.startswith('Ontology(') or line == ')':
                continue
            if class_decl.fullmatch(line): kind = 'class_declaration'
            elif role_decl.fullmatch(line): kind = 'role_declaration'
            elif named_sub.fullmatch(line): kind = 'named_subclass'
            elif any(pattern.fullmatch(line) for pattern in rbox): kind = 'accepted_rbox'
            elif line.startswith('Declaration('): kind = 'other_declaration'
            elif line.startswith('SubClassOf('): kind = 'complex_subclass'
            else: kind = 'other_axiom'
            counts[kind] += 1
            first.setdefault(kind, [number, line[:300]])
    print(json.dumps({'ontology':oid,'counts':dict(sorted(counts.items())),
                      'first':{k:first[k] for k in sorted(first)}},sort_keys=True))
print('DECLINE_AUDIT_COMPLETE')
PY
