"""fe_struct.py BASE.json NEW.json : check that NEW is BASE minus excluded middles
`-> Q(v) | A(v)` and with complement constraints `N(v) & Q(v) ->` rewritten to
`N(v) -> A(v)`, for definers Q whose definition clause `Q(v) & A(v) ->` is in both.
Prints dropped, rewritten, other (other must be 0)."""
import json, sys
from collections import Counter
def key(c):
    return json.dumps([sorted(json.dumps(a, sort_keys=True) for a in c['body']),
                       sorted(json.dumps(a, sort_keys=True) for a in c['head'])])
b = json.load(open(sys.argv[1]))['clauses']; n = json.load(open(sys.argv[2]))['clauses']
cb, cn = Counter(map(key, b)), Counter(map(key, n))
gone = cb - cn; new = cn - cb
def cpt(a): return a.get('kind') == 'concept' and a['term'].get('kind') == 'var'
defs = {}
for c in b:
    if not c['head'] and len(c['body']) == 2 and all(cpt(a) for a in c['body']):
        x, y = c['body']
        if x['term'] == y['term']:
            defs.setdefault(x['concept'], set()).add(y['concept']); defs.setdefault(y['concept'], set()).add(x['concept'])
dropped = rewritten = other = 0
expected_new = Counter()
for k, m in gone.items():
    body, head = json.loads(k)
    body = [json.loads(a) for a in body]; head = [json.loads(a) for a in head]
    if not body and len(head) == 2 and all(cpt(a) for a in head) and head[0]['term'] == head[1]['term'] \
            and (head[1]['concept'] in defs.get(head[0]['concept'], ())):
        dropped += m; continue
    if not head and len(body) == 2 and all(cpt(a) for a in body) and body[0]['term'] == body[1]['term']:
        ok = False
        for q, nn in ((body[0], body[1]), (body[1], body[0])):
            for a in defs.get(q['concept'], ()):
                if q['concept'].startswith('Q_') and nn['concept'] != a:
                    cand = key({'body': [nn], 'head': [{'kind': 'concept', 'concept': a, 'term': q['term']}]})
                    if new[cand] - expected_new[cand] >= m:
                        expected_new[cand] += m; ok = True; break
            if ok: break
        if ok: rewritten += m; continue
    other += m
other += sum((new - expected_new).values())
print(dropped, rewritten, other)
