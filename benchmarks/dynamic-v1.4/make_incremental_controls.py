#!/usr/bin/env python3
"""Analytic addition/deletion, RBox, ABox and expressive update controls."""
import hashlib
import json
from pathlib import Path
import sys

root=Path(sys.argv[1]).resolve();root.mkdir(parents=True,exist_ok=True)
prefix='Prefix(:=<urn:km:control:>)\nOntology(\n'
cases={}
chain=[f'SubClassOf(:C{i} :C{i+1})' for i in range(20)]
declarations=[f'Declaration(Class(:C{i}))' for i in range(21)]
cases['additions']=[declarations+chain[:i] for i in range(21)]
cases['deletions']=[declarations+chain[:i] for i in range(20,-1,-1)]
base=['SubClassOf(:A ObjectSomeValuesFrom(:r :B))',
      'SubClassOf(:B ObjectSomeValuesFrom(:s :C))',
      'SubClassOf(ObjectSomeValuesFrom(:t :C) :D)']
change=['SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)']
cases['rbox']=[base,base+change,base,base+change,base]
base=['DisjointClasses(:A :B)','ClassAssertion(:A :a)']
change=['ClassAssertion(:B :a)']
cases['abox']=[base,base+change,base,base+change,base]
base=['ObjectPropertyAssertion(:r :a :b)','ObjectPropertyAssertion(:r :a :c)',
      'DifferentIndividuals(:b :c)']
change=['FunctionalObjectProperty(:r)']
cases['equality']=[base,base+change,base,base+change,base]
base=['SubClassOf(:A ObjectUnionOf(:B :C))','SubClassOf(:B :D)','Declaration(Class(:D))']
change=['SubClassOf(:C :D)']
cases['disjunction']=[base,base+change,base,base+change,base]
manifest={}
for name,states in cases.items():
    out=root/name;out.mkdir(parents=True,exist_ok=True)
    paths=[];hashes={}
    for i,axioms in enumerate(states):
        p=out/f'state-{i:03}.ofn';p.write_text(prefix+'\n'.join(axioms)+'\n)\n')
        paths.append(str(p));hashes[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
    (out/'states.txt').write_text('\n'.join(paths)+'\n')
    (out/'pilot-states.txt').write_text('\n'.join(paths)+'\n')
    expected_consistency=[i%2==0 for i in range(len(states))] if name in ['abox','equality'] else [True]*len(states)
    manifest[name]={'states':len(states),'sha256':hashes,'consistent':expected_consistency,
        'restores_initial':name not in ['additions','deletions']}
(root/'controls.json').write_text(json.dumps(manifest,indent=2)+'\n')
