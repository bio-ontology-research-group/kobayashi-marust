"""Print a KM clause file (`km ofn` output) one clause per line.
usage: python3 -I show_clauses.py CLAUSES.json"""
import json, sys
def tm(x):
    k = x.get('kind')
    if k == 'var': return x['name']
    if k in ('ind', 'aux'): return '#' + x['name']
    if k == 'fun': return '%s(%s)' % (x['function'], tm(x['arg']))
    return json.dumps(x)
def at(x):
    if x['kind'] == 'concept': return '%s(%s)' % (x['concept'], tm(x['term']))
    if x['kind'] == 'role':
        a = [tm(v) for k, v in x.items() if isinstance(v, dict)]
        return '%s(%s)' % (x['role'], ','.join(a))
    a = [tm(v) for k, v in x.items() if isinstance(v, dict)]
    return '='.join(a)
d = json.load(open(sys.argv[1]))
for c in d['clauses']:
    print(' & '.join(map(at, c['body'])) or 'T', '->', ' | '.join(map(at, c['head'])) or 'F')
print('rbox', json.dumps(d.get('rbox'))[:400])
