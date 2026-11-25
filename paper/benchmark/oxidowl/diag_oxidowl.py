"""Per-class diagnosis of oxidowl hierarchies against a reference relation (untimed)."""
import gzip, json, sys, glob
from pathlib import Path
from urllib.parse import unquote
root = Path(sys.argv[1]); run = root / sys.argv[2]
OWL = 'http://www.w3.org/2002/07/owl#'; TOP, BOT = OWL + 'Thing', OWL + 'Nothing'
man = {r['ontology']: r for r in json.load(open(root / 'inputs/held-out-inputs.json'))['inputs']}
def closure(edges):
    adj = {}
    for a, b in edges: adj.setdefault(a, set()).add(b)
    out = {}
    for s in adj:
        seen, st = set(), [s]
        while st:
            for y in adj.get(st.pop(), ()):
                if y not in seen: seen.add(y); st.append(y)
        seen.discard(s); seen.discard(TOP); out[s] = seen
    return out
res = {}
for f in glob.glob(str(run / 'chunks/*.json')):
    for x in json.load(open(f))['outcomes']:
        o = x['ontology']
        if x['cls']['status'] != 'executed_unvalidated': continue
        try:
            ref = Path(man[o]['reference_directory'])
            classes = {l.split('\t')[1] for l in (ref / 'signature.tsv').read_text().splitlines() if l.startswith('C\t')}
            known = classes | {TOP, BOT}
            R = None
            for b in x.get('audit', {}).get('references', []):
                for p in (ref / (b + '.normalized.json'), ref / (b + '.normalized.json.gz')):
                    if p.is_file():
                        R = json.load(gzip.open(p) if p.suffix == '.gz' else open(p)); rb = b; break
                if R: break
            if not R: res[o] = {'error': 'no reference relation'}; continue
            if not R['consistent']: res[o] = {'reference': rb, 'reference_consistent': False}; continue
            raw = json.loads((run / o / 'cls/taxonomy.raw').read_text())
            fix = lambda i: next((c for c in (i, unquote(i), i.replace('file:///', 'file:/'), unquote(i).replace('file:///', 'file:/')) if c in known), None)
            edges, rescued, unknown_keys, anon = [], 0, 0, 0
            for k, v in raw.items():
                kk = fix(k)
                if kk is None: unknown_keys += 1; continue
                rescued += kk != k
                for s in v:
                    ss = fix(s)
                    if ss is None: anon += 1
                    elif ss != kk: edges.append((kk, ss))
            mine, theirs = closure(edges), closure([tuple(e) for e in R['subsumptions']])
            unsat = set(R['unsatisfiable'])
            miss = extra = both = 0; ex = []; missing_pairs = extra_pairs = 0; to_bot = 0
            for c in classes - unsat - {TOP, BOT}:
                m, t = mine.get(c, set()), theirs.get(c, set())
                a, b = t - m, m - t
                if BOT in b: to_bot += 1
                missing_pairs += len(a); extra_pairs += len(b)
                if a and b: both += 1
                elif a: miss += 1
                elif b: extra += 1
                if (a or b) and len(ex) < 3: ex.append([c, sorted(a)[:3], sorted(b)[:3]])
            res[o] = {'reference': rb, 'classes': len(classes), 'ref_unsat': len(unsat), 'rescued_iri_keys': rescued, 'unknown_keys': unknown_keys,
                      'only_missing': miss, 'only_extra': extra, 'both': both, 'missing_pairs': missing_pairs, 'extra_pairs': extra_pairs,
                      'ref_pairs': sum(len(v) for c, v in theirs.items() if c not in unsat), 'sat_class_under_nothing': to_bot,
                      'sample_unknown_key': next((k for k in raw if fix(k) is None), None), 'examples': ex}
        except Exception as e:
            res[o] = {'error': repr(e)}
json.dump(res, open(run / 'diagnosis.json', 'w'), indent=1)
print(len(res))
