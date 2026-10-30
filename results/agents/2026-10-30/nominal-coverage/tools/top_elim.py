"""Diagnostic: eliminate unit facts -> Q(x) (empty body, one variable atom) for
internal Q: drop Q(t) from every body, drop every clause with Q in its head.
usage: top_elim.py IN OUT [reserved names...]"""
import json, sys
d = json.load(open(sys.argv[1])); reserved = set(sys.argv[3:])
internal = lambda n: n.startswith('Q_')
tops = set()
for c in d['clauses']:
    if not c['body'] and len(c['head']) == 1:
        a = c['head'][0]
        if a['kind'] == 'concept' and a['term']['kind'] == 'var' and internal(a['concept']) and a['concept'] not in reserved:
            tops.add(a['concept'])
out = []
for c in d['clauses']:
    if any(a['kind'] == 'concept' and a['concept'] in tops for a in c['head']):
        continue
    c = dict(c); c['body'] = [a for a in c['body'] if not (a['kind'] == 'concept' and a['concept'] in tops)]
    out.append(c)
d['clauses'] = out
json.dump(d, open(sys.argv[2], 'w'))
print('tops', len(tops), sorted(tops)[:10], 'clauses', len(out))
