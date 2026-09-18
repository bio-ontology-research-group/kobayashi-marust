#!/usr/bin/env python3
"""Analytic controls with explicit complete support families under set semantics."""
import json,sys
from pathlib import Path
root=Path(sys.argv[1]).resolve();base=root/'justification-controls';base.mkdir(exist_ok=True)
ns='urn:km:just:';nothing='http://www.w3.org/2002/07/owl#Nothing';thing='http://www.w3.org/2002/07/owl#Thing'
paths=['SubClassOf(:A :B)','SubClassOf(:B :D)','SubClassOf(:A :C)','SubClassOf(:C :D)']
cases=[('two-paths',paths,ns+'A',ns+'D',[[0,1],[2,3]]),('noise',paths+['SubClassOf(:N%d :N%d)'%(i,i+1) for i in range(30)],ns+'A',ns+'D',[[0,1],[2,3]]),('negative',['SubClassOf(:A :B)'],ns+'A',ns+'D',[]),('unsatisfiable',['SubClassOf(:A :B)','SubClassOf(:A :C)','DisjointClasses(:B :C)'],ns+'A',nothing,[[0,1,2]]),('inconsistent',['SubClassOf(:A owl:Nothing)','ClassAssertion(:A :a)'],thing,nothing,[[0,1]]),('tautology',['SubClassOf(:A :B)'],ns+'A',ns+'A',[[]])]
for index,(name,axioms,sub,sup,families) in enumerate(cases):
 source=base/(name+'.ofn');source.write_text('Prefix(:=<urn:km:just:>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(\n'+'\n'.join(axioms)+'\n)\n')
 task={'input':str(source),'sub':sub,'super':sup,'el':True,'library':True,'limits':[1,10],'repetition':0,'km':'/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex','runtime':'/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes','classes':str(base/('classes-%02d'%index)),'konclude':str(root/'konclude_oracle.py'),'expected_supports':[[axioms[i] for i in family] for family in families],'control':name}
 (base/('%02d.json'%index)).write_text(json.dumps(task,indent=2)+'\n')
