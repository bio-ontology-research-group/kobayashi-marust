"""Markdown table from timing.sh outputs (v154.tsv, rc.tsv)."""
import sys, re
def load(p):
    rows = {}
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        get = lambda k: next((x.split('=', 1)[1] for x in f if x.startswith(k + '=')), '')
        d = re.search(r'dropped=(\d+)', line)
        rows[f[0]] = dict(rc=get('rc'), wall=get('wall'), dropped=d.group(1) if d else '-',
                          route=next((x[6:] for x in f if x.startswith('route=')), ''), verdict=f[-1])
    return rows
a, b = load(sys.argv[1]), load(sys.argv[2])
print('| Input | v1.5.4 wall (s) | v1.5.4 outcome | v1.5.5 wall (s) | v1.5.5 outcome |')
print('|---|---|---|---|---|')
def outcome(r):
    if r['rc'] == '124': return 'no answer (timeout)'
    if r['rc'] != '0': return 'exit ' + r['rc']
    v = r['verdict'].replace('(dropped-stripped)', '')
    agree = ', '.join(x.split('=')[0] for x in v.split(',') if x.endswith('True'))
    return f"DROPPED {r['dropped']}, {r['route']}, taxonomy agrees with {agree}" if r['dropped'] not in ('0', '-') else f"exact, {r['route']}, agrees with {agree}"
for k in a:
    print(f"| `{k}` | {a[k]['wall']} | {outcome(a[k])} | {b.get(k, {}).get('wall', '')} | {outcome(b[k]) if k in b else ''} |")
