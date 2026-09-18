#!/usr/bin/env python3
"""Build analytic adapter controls with independently specified expected taxonomy."""
from pathlib import Path
import sys
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
ref = out / 'expected'
ref.mkdir(exist_ok=True)
consistent = '''Prefix(:=<urn:control:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
Declaration(Class(:D)) Declaration(Class(:T)) Declaration(Class(:U))
EquivalentClasses(:A :B) SubClassOf(:B :C)
EquivalentClasses(:T owl:Thing) EquivalentClasses(:U owl:Nothing)
)
'''
inconsistent = '''Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(SubClassOf(owl:Thing owl:Nothing))
'''
(out / 'consistent.ofn').write_text(consistent)
(out / 'inconsistent.ofn').write_text(inconsistent)
(out / 'states.txt').write_text(str(out / 'consistent.ofn') + '\n' + str(out / 'inconsistent.ofn') + '\n')
rows = {'C\ttrue', 'U\turn:control:U'}
for a,b in [('A','B'),('B','A'),('A','C'),('B','C'),('A','T'),('B','T'),('C','T'),('D','T')]:
    rows.add(f'S\turn:control:{a}\turn:control:{b}')
(ref / '000.sig').write_text('\n'.join(sorted(rows)) + '\n')
(ref / '001.sig').write_text('C\tfalse\n')
