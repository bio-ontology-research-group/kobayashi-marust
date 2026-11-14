"""Compare `km classify --lines --properties` rows with HermiT rows
(run_hermit_props.sh).
usage: compare_properties.py ontology.ofn km_output hermit_output
Prints only-km and only-hermit rows after expanding km prefixed names."""
import re, sys
ont, kmf, hf = sys.argv[1:4]
prefixes = {}
with open(ont, errors='replace') as f:
    for line in f:
        m = re.match(r'\s*Prefix\(\s*([^:]*):=\s*<([^>]*)>\s*\)', line)
        if m: prefixes[m.group(1)] = m.group(2)
        elif line.startswith('Ontology('): break
def expand(tok):
    m = re.fullmatch(r'ObjectInverseOf\((.*)\)', tok)
    if m: return 'ObjectInverseOf(%s)' % expand(m.group(1))
    if tok.startswith('<') and tok.endswith('>'): return tok[1:-1]
    if ':' in tok:
        p, l = tok.split(':', 1)
        if p in prefixes and not l.startswith('//'): return prefixes[p] + l
    return tok
KINDS = ('SUBPROP', 'TOPPROP', 'BOTPROP', 'DOMAIN', 'RANGE', 'CONSISTENT')
def rows(path, exp):
    out = set()
    for line in open(path):
        line = line.rstrip('\n')
        parts = line.split('\t') if '\t' in line else line.split(' ')
        if parts[0] not in KINDS: continue
        if parts[0] == 'CONSISTENT': out.add(line); continue
        out.add('\t'.join([parts[0]] + [exp(p) for p in parts[1:]]))
    return out
k = rows(kmf, expand); h = rows(hf, lambda t: t)
hb = {r.split('\t')[1] for r in h if r.startswith('BOTPROP\t')}
h = {r for r in h if r.startswith(('BOTPROP', 'CONSISTENT', 'TOPPROP')) or r.split('\t')[1] not in hb}
ok, oh = sorted(k - h), sorted(h - k)
print(f"rows km={len(k)} hermit={len(h)} common={len(k & h)} only_km={len(ok)} only_hermit={len(oh)}")
for r in ok: print('KM-ONLY\t' + r)
for r in oh: print('HERMIT-ONLY\t' + r)
