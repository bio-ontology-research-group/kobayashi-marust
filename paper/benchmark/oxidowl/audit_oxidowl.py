"""Check one oxidowl answer against the pinned reference answers (untimed).

Inputs in --out: cls/taxonomy.raw (JSON written by `oxidowl classification -o`:
class IRI -> list of all its superclasses) and ku/taxonomy.raw (stdout of
`oxidowl -k -U`: consistency verdict and unsatisfiable classes).

Two checks, both with the protocol's canonicalize.py / full_iri_fingerprint.py:
  strict   consistency + unsatisfiable classes + all subsumptions between named
           classes, compared with compare() exactly as the KM and Konclude runs.
  taxonomy the classification file alone: for every class that the reference
           finds satisfiable, the set of its named superclasses must equal the
           reference's. Unsatisfiable classes and consistency are not checked.
"""
import argparse, gzip, json, re, sys
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--out', type=Path, required=True)
ap.add_argument('--reference', type=Path, required=True)
ap.add_argument('--protocol', type=Path, required=True)
ap.add_argument('--strict', action='store_true')
a = ap.parse_args()
sys.path.insert(0, str(a.protocol))
from canonicalize import canonicalize  # noqa: E402
from compare_taxonomies import compare  # noqa: E402
from measure_classification import digest  # noqa: E402

OWL = 'http://www.w3.org/2002/07/owl#'
TOP, BOTTOM = OWL + 'Thing', OWL + 'Nothing'
REFS = ['konclude', 'hermit', 'openllet', 'jfact']
res = {'strict': {}, 'taxonomy': {}}
sig = a.reference / 'signature.tsv'
classes = {l.split('\t')[1] for l in sig.read_text().splitlines() if l.startswith('C\t')}
known = classes | {TOP, BOTTOM}
fp = a.protocol / 'full_iri_fingerprint.py'

raw = json.loads((a.out / 'cls' / 'taxonomy.raw').read_text())
edges, dropped_keys, dropped_supers = [], 0, 0
for sub, sups in raw.items():
    if sub not in known:
        dropped_keys += 1
        continue
    for sup in sups:
        if sup not in known:
            dropped_supers += 1
        elif sup != sub:
            edges.append([sub, sup])
res.update(keys=len(raw), signature_classes=len(classes), dropped_keys=dropped_keys,
           dropped_supers=dropped_supers, missing_classes=len(classes - set(raw)))


def write(name, consistent, unsat):
    p = a.out / (name + '.raw.json')
    p.write_text(json.dumps({'consistent': consistent, 'subsumptions': edges, 'unsatisfiable': sorted(unsat)}))
    return canonicalize(p, 'km-json', sig, a.out / name, fp)


audit = json.loads((a.reference / 'audit.json').read_text())
usable = [b for b in REFS if audit['outcomes'].get(b, {}).get('status') == 'canonicalized_requires_comparison'
          and digest(a.reference / (b + '.validated.json')) == audit['outcomes'][b]['canonical_sha256']]
res['references'] = usable


def lines(path):
    with gzip.open(path, 'rt', encoding='utf-8') as h:
        return dict(l.rstrip('\n').split('\t', 1) for l in h if l.strip())


def names(path):
    with gzip.open(path, 'rt', encoding='utf-8') as h:
        return {l.rstrip('\n') for l in h if l.strip()}


# taxonomy-only check
try:
    write('tax', True, [])
    mine, mine_unsat = lines(str(a.out / 'tax') + '.nodes.tsv.gz'), names(str(a.out / 'tax') + '.unsat.txt.gz')
    res['own_unsat_in_classification_file'] = len(mine_unsat)
    for b in usable:
        ref = json.loads((a.reference / (b + '.validated.json')).read_text())
        if not ref.get('consistent'):
            res['taxonomy'][b] = {'status': 'reference_inconsistent', 'agreement': None}
            continue
        rl, ru = lines(a.reference / (b + '.nodes.tsv.gz')), names(a.reference / (b + '.unsat.txt.gz'))
        missing = sum(1 for c, v in rl.items() if mine.get(c) != v)          # satisfiable class, different or absent superclass set
        extra = sum(1 for c in mine if c not in rl and c not in ru)           # superclasses where the reference has none
        wrongly_unsat = len(mine_unsat - ru)
        res['taxonomy'][b] = {'status': 'compared', 'agreement': missing == 0 and extra == 0 and wrongly_unsat == 0,
                              'classes_differing': missing, 'classes_with_extra_superclasses': extra,
                              'wrongly_unsatisfiable': wrongly_unsat, 'reference_classes_with_superclasses': len(rl),
                              'reference_unsatisfiable': len(ru)}
except Exception as error:
    res['taxonomy_error'] = repr(error)

# strict check
if a.strict:
    try:
        text = (a.out / 'ku' / 'taxonomy.raw').read_text(errors='replace')
        m = re.search(r'Consistency check: (CONSISTENT|INCONSISTENT)', text)
        if not m or 'Unsatisfiable classes:' not in text:
            raise ValueError('no consistency verdict or unsatisfiable list in output')
        consistent = m.group(1) == 'CONSISTENT'
        listed = []
        for line in text.split('Unsatisfiable classes:', 1)[1].splitlines()[1:]:
            if not line.startswith('  '):
                break
            listed.append(line[2:])
        unsat = {x for x in listed if x in classes}
        res.update(reported_consistent=consistent, reported_unsatisfiable=len(unsat),
                   unsat_lines_not_in_signature=len([x for x in listed if x not in classes and x != 'Nothing']))
        answer = write('strict', consistent, unsat)
        for b in usable:
            res['strict'][b] = compare(answer, json.loads((a.reference / (b + '.validated.json')).read_text()))
    except Exception as error:
        res['strict_error'] = repr(error)
(a.out / 'oxidowl-audit.json').write_text(json.dumps(res, indent=1) + '\n')
