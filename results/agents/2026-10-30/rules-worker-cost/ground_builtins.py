"""HermiT has no SWRL built-ins. Rewrite each rule of a gen_finite_rules.py
ontology into builtin-free rules: the data variable `n` of the comparison
`n op c` is replaced by every integer literal of the ontology's data
assertions that satisfies it (DL-safe data variables only bind to asserted
values, which is also the grounding KM certifies).

usage: python3 -I ground_builtins.py IN.ofn OUT.ofn
"""
import re
import sys

OPS = {'equal': lambda a, b: a == b, 'notEqual': lambda a, b: a != b,
       'lessThan': lambda a, b: a < b, 'greaterThan': lambda a, b: a > b,
       'greaterThanOrEqual': lambda a, b: a >= b}
text = open(sys.argv[1]).read()
values = sorted({int(v) for v in re.findall(r'DataPropertyAssertion\([^"]*"(-?\d+)"\^\^xsd:integer\)', text)})
out = []
for line in text.splitlines():
    m = re.search(r' BuiltInAtom\(<http://www.w3.org/2003/11/swrlb#(\w+)> (Variable\(<[^>]*>\)) "(-?\d+)"\^\^xsd:integer\)', line)
    if not line.startswith('DLSafeRule(') or not m:
        out.append(line)
        continue
    op, var, c = m.group(1), m.group(2), int(m.group(3))
    base = line.replace(m.group(0), '')
    for k in values:
        if OPS[op](k, c):
            out.append(base.replace(var, f'"{k}"^^xsd:integer'))
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
